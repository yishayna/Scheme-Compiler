#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let const_offset = ref 0 ;;
  let next_const_offset off = let v = !const_offset in
    (const_offset:= v+off ; v);;

  let fvar_offset = ref 0 ;;
  let fvar_next_offset()= let v = !fvar_offset in
    (fvar_offset:= v+1 ; v);;

  let lable_id = ref 0 ;;
  let next_lable_id() = let v= !lable_id in
    (lable_id:= v+1 ; !lable_id);;


  let rec get_tbl e tbl adder  =
    match e with
    | Const'(s)-> (adder e tbl)
    | Var'(VarFree v) -> (adder e tbl)
    | BoxSet'(_,e) -> get_tbl e tbl adder
    | If'(test, dit, dif)-> map_flat (fun e -> get_tbl e tbl adder) [test; dit; dif]
    | (Seq'(l) | Or'(l)) -> map_flat (fun e -> get_tbl e tbl adder) l
    | (Set'(_, e) | Def'(_, e)) ->  get_tbl e tbl adder
    | LambdaSimple'(_, body) -> get_tbl body tbl adder
    | LambdaOpt'(_, _, body) -> get_tbl body tbl adder
    | (Applic'(first, sexprs) | ApplicTP'(first, sexprs)) -> map_flat (fun e -> get_tbl e tbl adder) (first::sexprs)
    | _ -> tbl
  
    and map_flat f lst = (remove_dup (List.flatten (List.map f lst)))

    and remove_dup lst = List.fold_left (fun acc expr -> if (List.mem_assoc (fst expr) acc)  then acc else (expr::acc))  [] lst 
  
  let  idx_as_int expr tbl = (fst (List.assoc expr tbl));;
  let  idx_as_str expr tbl =  try (string_of_int (idx_as_int expr tbl)) with Not_found -> "ERROR idx_as_str"  ;;

  let rec add_to_const_tbl expr tbl =
      match expr with
      | Char(c) ->  append_to_set (Sexpr(expr), (next_const_offset 2, "MAKE_LITERAL_CHAR("^(string_of_int (Char.code c))^")"))  tbl
      | Number(Float f) -> append_to_set (Sexpr(expr),(next_const_offset 9, "MAKE_LITERAL_FLOAT("^(string_of_float f)^")"))  tbl
      | Number(Fraction (n, d)) -> append_to_set (Sexpr(expr),(next_const_offset 17, "MAKE_LITERAL_RATIONAL("^string_of_int n^","^string_of_int d^")"))  tbl
      | String(s) ->  append_to_set (Sexpr(expr),(next_const_offset ((String.length s) + 9), "MAKE_LITERAL_STRING \""^(String.escaped s)^"\""))  tbl
      | Symbol(s) ->  (let n_tbl = add_to_const_tbl (String(s)) tbl in
                      append_to_set (Sexpr(expr),(next_const_offset 9,"MAKE_LITERAL_SYMBOL(const_tbl+"^(idx_as_str (Sexpr(String(s))) n_tbl)^")"))  n_tbl)
      | Pair(car, cdr) ->  (let n_tbl = (add_to_const_tbl car (add_to_const_tbl cdr tbl)) in 
                            append_to_set (Sexpr(expr),(next_const_offset 17,"MAKE_LITERAL_PAIR(const_tbl+"^(idx_as_str (Sexpr(car)) n_tbl)^",const_tbl+"^(idx_as_str (Sexpr(cdr)) n_tbl)^")"))  n_tbl)
      | _ -> tbl

    and append_to_set (a,(b,c)) tbl = if (List.mem_assoc a tbl) then tbl else  ((a,(b,c)):: tbl) 
  
  let const_tbl_adder e tbl = 
    match e with 
    | Const'(Sexpr(expr)) -> (add_to_const_tbl expr tbl)
    | _ -> tbl

  let fvar_tbl_adder e tbl = 
    match e with 
    | Var'(VarFree v) when (List.mem_assoc v tbl == false) -> ((v, fvar_next_offset()) :: tbl)
    | _ -> tbl
 
  let print  = Printf.sprintf;;
  let print_lst lst =  String.concat "\n" lst ;; 


  let rec generate_rec consts fvars e count =
    let generate_rec e = generate_rec consts fvars e count in
    match e with
    | Const'(c) -> print "mov rax, const_tbl+%s ; generate Const'(c)" (idx_as_str c consts)
    | Var'(VarFree (v)) -> print "mov rax, qword [fvar_tbl+ WORD_SIZE * %s] ; generate Var'(VarFree (v))" (idx_as_str v fvars)
    | Var'(VarParam (v,mn)) -> print "mov rax, qword [rbp+ WORD_SIZE * (4 + %d)] ; generate Var'(VarParam (v,mn))" mn
    | Var'(VarBound (v,major,minor)) -> 
          print_lst 
            [ "; generate Var'(VarBound (v,major,minor))";
              print " mov rax, qword [rbp+ WORD_SIZE * 2]" ;
              print " mov rax, qword [rbp+ WORD_SIZE * %d]" major;
              print " mov rax, qword [rbp+ WORD_SIZE * %d]" minor;]
                      
    
    | (Set'(VarFree (v), e) | Def'(VarFree (v), e)) ->
          print_lst 
            [ "; generate Set'(Var'(VarFree (v)), e)";
              print " %s \n" (generate_rec e) ;
              print " mov qword [%s], rax" (idx_as_str v fvars);
              print " mov rax, SOB_VOID_ADDRESS";]


    | Set'(VarParam (_,mn), e) -> 
          print_lst 
            [ "; generate Set'(Var'(VarParam (_,mn)), e)";
              print " %s \n" (generate_rec e) ;
              print " mov qword [rbp+ WORD_SIZE * (4 + %d)], rax" mn;
              print " mov rax, SOB_VOID_ADDRESS";]

    | Set'(VarBound (v,major,minor),e) -> 
          print_lst 
            [ "; generate  Set'(Var'(VarBound (v,major,minor)),e)";
              print " %s \n" (generate_rec e) ;
              print " mov rbx, qword [rbp+ WORD_SIZE * 2]" ;
              print " mov rbx, qword [rbp+ WORD_SIZE * %d]" major;
              print " mov qword [rbp+ WORD_SIZE * %d], rax" minor;
              " mov rax, SOB_VOID_ADDRESS";]



    | Seq'(l)-> print_lst (List.map generate_rec l)

    | Or'(l)-> let id = next_lable_id() in 
          print_lst 
            [ "; generate  Or'(l)";
              print_lst (List.map (fun e -> (print "%s\n mov rax, SOB_FALSE_ADDRESS \n jne Lexit%d:" (generate_rec e) id )) l) ;
              print "Lexit%d:" id]

    
    | If'(test, dit, dif)-> let id = next_lable_id() in 
          print_lst 
            [ "; generate  If'(test, dit, dif)";
              (generate_rec test);
              "cmp rax, SOB_FALSE_ADDRESS";
              print "je Lelse%d: " id ;
              (generate_rec dit);
               print "je Lexit%d:\nLelse%d:" id id;
              (generate_rec dif);
              print "Lexit%d:" id;]

    
    | BoxGet'(v) -> print_lst [ "; generate  Boxget'(v)";  (generate_rec (Var'(v))); "mov rax, qword [rax]";]

    | BoxSet'(v,e) -> 
        print_lst 
          [";generate  BoxSet'(v,e)";
            (generate_rec e);
            "push rax";
            (generate_rec (Var'(v)));
            "pop qword [rax]";
            "mov rax, SOB_VOID_ADDRESS";]

    
    (*

    | LambdaSimple'(_, body) -> 
    | LambdaOpt'(_, _, body) -> 
    | (Applic'(first, sexprs) 
    | ApplicTP'(first, sexprs)) ->  *)
     
    | _ -> "tbl"
  

  
  
  let make_consts_tbl asts =
    let consts_tbl_init = 
      [ (Void, (next_const_offset 1, "MAKE_VOID")); 
        (Sexpr (Nil), (next_const_offset 1, "MAKE_NIL")); 
        (Sexpr(Bool false), (next_const_offset 2, "MAKE_BOOL(0)")); 
        (Sexpr(Bool true), (next_const_offset 2,"MAKE_BOOL(1)")); 
      ] in
    
    let adrs_sort = List.sort (fun (a1,(b1,c1)) (a2,(b2,c2)) -> if b1 > b2 then 1 else 0) in
    adrs_sort (List.fold_left (fun tbl e -> get_tbl e tbl const_tbl_adder) consts_tbl_init asts);; 
    
  let make_fvars_tbl asts = 
    let primitive_fvar_table = List.map (fun a -> (a, fvar_next_offset()))
      [
        (* Type queries  *)
        "boolean?"; "flonum?"; "rational?"; "pair?"; "null?"; "char?"; "string?"; "procedure?"; "symbol?"; 
        (* String procedures *)
        "string-length"; "string-ref"; "string-set!"; "make-string"; "symbol->string";
        (* Type conversions *)
        "char->integer"; "integer->char"; "exact->inexact";
        (* Identity test *)
        "eq?"; 
        (* Arithmetic ops *)
        "+"; "*"; "/"; "="; "<"; 
        (* Additional rational numebr ops *)
        "numerator"; "denominator"; "gcd"; 
        (* you can add yours here *)
        "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; ] in   

        (List.fold_left (fun tbl e -> get_tbl e tbl fvar_tbl_adder) primitive_fvar_table asts);; 
  
  
  
        let generate consts fvars e = "raise X_not_yet_implemented";;
end;;


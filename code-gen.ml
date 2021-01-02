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
    | Var'(v) -> (adder e tbl)
    | Box'(v) -> (adder (Var' v) tbl)
    | BoxGet'(v) -> (adder (Var' v) tbl)
    | BoxSet'(v,e) -> get_all_tbl [ (Var' v); e] tbl adder  
    | If'(test, dit, dif)-> get_all_tbl [test; dit; dif] tbl adder  
    | (Seq'(l) | Or'(l)) ->  get_all_tbl l tbl adder 
    | (Set'(v, e) | Def'(v, e)) -> get_all_tbl [(Var' v);e] tbl adder 
    | LambdaSimple'(_, body) -> get_tbl body tbl adder
    | LambdaOpt'(_, _, body) -> get_tbl body tbl adder
    | (Applic'(first, sexprs) | ApplicTP'(first, sexprs)) ->  get_all_tbl (first::sexprs) tbl adder 
    | _ -> tbl
  
    and get_all_tbl lst tbl adder  = (List.fold_right (fun e acc ->  (get_tbl e acc adder)) lst tbl)
    
    (* and map_flat f lst = (remove_dup (List.flatten (List.map f lst)))
    and remove_dup lst =   List.fold_left (fun acc expr -> if (List.mem_assoc (fst expr) acc)  then acc else (expr::acc))  [] lst  *)
  
  let  idx_as_int expr tbl = (fst (List.assoc expr tbl));;
  let  idx_as_str expr tbl =  try (string_of_int (idx_as_int expr tbl)) with Not_found -> "ERROR idx_as_str"  ;;
  let  idx_as_str_fvars expr tbl =  try (string_of_int (List.assoc expr tbl)) with Not_found -> ("ERROR_idx_as_str "^expr)  ;;


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
    | Var'(VarFree v) when (List.mem_assoc v tbl = false) -> tbl@[(v, fvar_next_offset())]
    | _ -> tbl
 
  let print  = Printf.sprintf;;
  let print_lst lst =  String.concat "\n" lst ;; 


  let rec generate_rec consts fvars e env_num =
    let generate_rec_call e =  generate_rec consts fvars e env_num in
    match e with
    | Const'(c) -> print "mov rax, [const_tbl+%s] ; generate Const'(c)" (idx_as_str c consts)
    | Var'(VarFree (v)) -> print "mov rax, qword [fvar_tbl+ WORD_SIZE * %s] ; generate Var'(VarFree (v))" (idx_as_str_fvars v fvars)
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
              print " %s \n" (generate_rec_call e) ;
              print " mov qword [%s], rax" (idx_as_str_fvars v fvars);
              print " mov rax, SOB_VOID_ADDRESS";]


    | Set'(VarParam (_,mn), e) -> 
          print_lst 
            [ "; generate Set'(Var'(VarParam (_,mn)), e)";
              print " %s \n" (generate_rec_call e) ;
              print " mov qword [rbp+ WORD_SIZE * (4 + %d)], rax" mn;
              print " mov rax, SOB_VOID_ADDRESS";]

    | Set'(VarBound (v,major,minor),e) -> 
          print_lst 
            [ "; generate  Set'(Var'(VarBound (v,major,minor)),e)";
              print " %s \n" (generate_rec_call e) ;
              print " mov rbx, qword [rbp+ WORD_SIZE * 2]" ;
              print " mov rbx, qword [rbp+ WORD_SIZE * %d]" major;
              print " mov qword [rbp+ WORD_SIZE * %d], rax" minor;
              " mov rax, SOB_VOID_ADDRESS";]



    | Seq'(l)-> print_lst (List.map generate_rec_call l)

    | Or'(l)-> let id = next_lable_id() in 
          print_lst 
            [ "; generate  Or'(l)";
              print_lst (List.map (fun e -> (print "%s\n mov rax, SOB_FALSE_ADDRESS \n jne Lexit%d" (generate_rec_call e) id )) l) ;
              print "Lexit%d:" id]

    
    | If'(test, dit, dif)-> let id = next_lable_id() in 
          print_lst 
            [ "; generate  If'(test, dit, dif)";
              (generate_rec_call test);
              "cmp rax, SOB_FALSE_ADDRESS";
              print "je Lelse%d " id ;
              (generate_rec_call dit);
               print "je Lexit%d\nLelse%d:" id id;
              (generate_rec_call dif);
              print "Lexit%d:" id;]

    
    | BoxGet'(v) -> print_lst [ "; generate  Boxget'(v)";  (generate_rec_call (Var'(v))); "mov rax, qword [rax]";]

    | BoxSet'(v,e) -> 
        print_lst 
          [";generate  BoxSet'(v,e)";
            (generate_rec_call e);
            "push rax";
            (generate_rec_call (Var'(v)));
            "pop qword [rax]";
            "mov rax, SOB_VOID_ADDRESS";]

    
    | LambdaSimple'(args, body) -> lambda_writer consts fvars env_num args body []
    | LambdaOpt'(args, opt , body) -> lambda_writer consts fvars env_num args body [opt]
    | Applic'(first, sexprs) -> applic_writer consts fvars env_num first sexprs false
    | ApplicTP'(first, sexprs) ->  applic_writer consts fvars env_num first sexprs true
     
    | _ -> ""
  
  
  
  and make_ext_env env_num id =
    let copy_minors = print_lst
                        [ "; generate - make_ext_env - copy_minors";
                          "; invariant: rbx hold EXT_ENV[0]";
                          "push rbx                     ; backup rbx";
                          "mov rax, LAST_ENV";
                          "mov rcx, 0                   ; i = 0 ";
                          "mov rdx, WORD_SIZE";
                          "add rdx, rbx                 ; rdx = ExtEnv[j], j = 1";
                          print "copy_minors%d:" id ;
                          "mov r8, rcx                  ; load the index (in bites) to r8" ;
                          "add r8, rax                  ; set r8 to point to the specific source cell ENV[i]  (i=j-1)";
                          "mov r8, [r8]                 ; copy the content of ENV[i] to r8";
                          "mov [rdx], r8                ; set the content of EXT_ENV[j] to the content of ENV[i]";
                          "add rdx, WORD_SIZE           ; prepare rdx to the next loop" ;           
                          "add rcx, WORD_SIZE           ; prepare rcx to the next loop" ;           
                          print "cmp rcx, WORD_SIZE*%d            ; while i<|ENV|" env_num;
                          print "jne copy_minors%d" id ;
                          "pop rbx                      ; load rbx from backup ";] in
  
    let copy_params = print_lst 
                        [ "; generate - make_ext_env - copy_params";
                          "; invariant: rbx hold EXT_ENV[0]";
                          "push rbx                       ; backup rbx";
                          "mov rcx, NUM_OF_ARGS";
                          "inc rcx                        ; reserve one WORD for the magic" ;            
                          "shl rcx, 3";
                          print "MALLOC rax, rcx" ;
                          "mov [rbx], rax                 ; set EXT_ENV[0] to point on new vector of size WORD_SIZE*(NUM_OF_ARGS+1)";
                          "mov rax, [rbx]                 ; rax = EXT_ENV[0][0]";
                          "lea rdx, FIRST_ARG_ON_STACK";
                                                    
                          "mov rcx, 0";
                          print "copy_params%d:" id ;
                          "mov r8, NUM_OF_ARGS";
                          "cmp rcx, r8";
                          print "je all_params_copied%d" id ;
                          "mov r8, [rdx + WORD_SIZE*rcx] ; load r8 with the content of ARGS[i]";
                          "mov [rax + WORD_SIZE*rcx], r8 ; copy EXT_ENV[0][i] = ARGS[i]";
                          "inc rcx";
                          print "jmp copy_params%d" id ;
                          print "all_params_copied%d:" id;
                          "pop rbx                        ; load rbx from backup ";] in

      print_lst 
        [";generate  make_ext_env";
          print "MALLOC rbx, WORD_SIZE*%d" (env_num + 1);
          (copy_params);
          (copy_minors);
        ]



  and adjust_stack num_of_args id =
    (*Invariant: These "OCAML MACROS" using r10+ registers unless it explicitly mentioned in the name  *)
    let num_args_stack_in_bites_to_r10 = "mov r10, NUM_OF_ARGS \n shl r10, 3" in 
    let args_diff_to_rcx =  (print "mov rcx, NUM_OF_ARGS \nsub rcx, %s" num_of_args) in
    let last_arg_pointer_to_r12 = print_lst ["lea r12, FIRST_ARG_ON_STACK"; (num_args_stack_in_bites_to_r10); "add r12, r10"] in
    
    let shrink_extra_args_to_lst_in_rax = 
        print_lst 
          [";generate  adjust_stack";
          "; invariant: after calling rax holding the new args pairs list";
          (last_arg_pointer_to_r12);
            "mov r9, SOB_NIL_ADDRESS           ; we want to build an proper list, so the last val is NIL"; 
            (args_diff_to_rcx);
            print "adjust_loop%d: \n cmp rcx, 0" id;
            print "je shrink_stack_end%d" id;
            "mov r8, [rbx]";
            "MAKE_PAIR(rax,r8,r9)               ; rax = pointer to the new pair, r8 = car, r9 = cdr";
            "mov r9, rax                        ; to make the list we need to add this list to be the cdr in the next loop";
            "sub r12, WORD_SIZE                 ; decrease r12 to point on the previos element for the next loop";
            print "dec rcx \n jmp adjust_loop%d" id;
            print "shrink_stack_end%d:" id;] in

    let enlarge_frame_and_finish_if_nedded =
        print_lst 
          [ (args_diff_to_rcx);
            "cmp rcx, 0                       ; we don't using opt args -> magic cell get an empty list";
            print "jne continue_adjust_stack%d" id;
            "mov r13, SOB_NIL_ADDRESS         ;"  ;
            (last_arg_pointer_to_r12);
            "add r12, WORD_SIZE";
            "mov qword [r12], r13" ;
            (print "jmp adjust_stack_end%d" id);] in
      
    
    let update_num_of_args_in_stack = 
        print_lst 
        [";generate  update_num_of_args_in_stack";
         print "lea rbx, NUM_OF_ARGS" ;
         print "mov qword [rbx], %d           ; num of requierd args + 1 for opt" ((int_of_string num_of_args) + 1);
        ] in

    let shrink_frame =  
      print_lst 
      [";generate  shrink_frame";
        (last_arg_pointer_to_r12);
        "mov qword [r12], rax                 ; set the last arg to be the pair list of optional args";
        "sub r12, WORD_SIZE                   ; this is now the last free cell for shrinking ";                  
        "mov rbx, rbp                         ; get the first element from stack to shrink";
        (args_diff_to_rcx);
        (print "shrink_frame%d:" id);
        "cmp rcx, 0";
        (print "je adjust_stack_end%d" id);
        "mov r10, [rbx]                       ; r10 <- current value to move up";
        "mov qword [r12], r10                 ; r12 holds the last free cell foor shrink";
        "sub r12, WORD_SIZE";
        "add rbx, WORD_SIZE                   ; go the the next element for shrinking";
        "add rbp, WORD_SIZE                   ; delete old element from stack";
        "dec rcx";
        (print "jmp shrink_frame%d" id);
        ] in
   
   
    print_lst 
        [";generate  adjust_stack";
          (shrink_extra_args_to_lst_in_rax);
          (enlarge_frame_and_finish_if_nedded);

          print "continue_adjust_stack%d:" id;
          (update_num_of_args_in_stack);
          (shrink_frame);
          (print "adjust_stack_end%d:" id);
          ] 

   

  and lambda_writer consts fvars env_num args body opt =
    let id = next_lable_id() in 
    let num_of_args = (string_of_int (List.length args)) in
    let ext_env_to_rbx =  if env_num = 0 then "mov rbx, SOB_VOID_ADDRESS" else (make_ext_env env_num  id) in
    let adjust_stack_if_needed = (if opt = [] then "" else (adjust_stack num_of_args id)) in
    let jump_error_if_illegal_args_count =  (if opt = [] then "jne illegal_args_count" else "jl illegal_args_count") in
    let body_code =  (generate_rec consts fvars body (env_num + 1)) in

    print_lst 
    [";generate  lambda_writer";
      ext_env_to_rbx;
      print "MAKE_CLOSURE(rax,rbx, Lcode%d)" id ;
      print " jmp Lcont%d "  id ;
      print "Lcode%d:" id ;
      "push rbp";
      "mov rbp, rsp";
      print "cmp qword NUM_OF_ARGS, %s" num_of_args;
      jump_error_if_illegal_args_count;
      adjust_stack_if_needed;
      body_code;
      "leave";
      "ret";
      print "Lcont%d:"  id ;
      (* RETURN VALUE????*)
     ]
  
  
  
  and finish_applic_not_TP = 
    print_lst 
    [";generate  finish_applic_not_TP";
      "add rsp, WORD_SIZE             ; pop env";
      "pop rbx                        ; pop arg count";
      "add rbx, 1                     ; adding one for the magic cell";
      "shl rbx, 3";
      "add rsp, rbx                   ; pop args";
      (* RETURN VALUE????*)

    ]
  
 and finish_applic_TP = 
    let fix_the_stack = "" in

    print_lst 
    [";generate  finish_applic_TP";
      "push qword [rbp+ WORD_SIZE]    ; old  ret addr";
      (fix_the_stack);
      "jmp rax                        ; code";
      (* RETURN VALUE????*)

    ]


  and applic_writer consts fvars env_num first sexprs is_TP =
      let id = next_lable_id() in 
      let args_gen =  List.map (fun e -> (generate_rec consts fvars e env_num)) (List.rev sexprs) in
      let args_code = (if sexprs = [] then "" else (String.concat "\npush rax\n" args_gen)^"\npush rax\n" ) in
      let proc_code = (generate_rec consts fvars first env_num) in
      let finish_applic_case =  (if is_TP = true then finish_applic_TP else finish_applic_not_TP) in

      print_lst 
        [";generate  applic_writer";
          (args_code);
          print "push %d" (List.length sexprs);
          (proc_code);
          "mov bl,byte [rax]";
          "cmp bl ,T_CLOSURE";
          "jne rax_isnt_closure";
          "push rax                 ; push env";
          (finish_applic_case);
        ]

       
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
  
  
        let generate consts fvars e =  (generate_rec consts fvars e 0);;
end;;


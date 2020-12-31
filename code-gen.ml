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
  let fvar_next_offset = let v = !fvar_offset in
    (fvar_offset:= v+1 ; v);;

  let primitive_fvar_table =  
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
      "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!";
    ]
    
    

    let rec get_tbl e tbl adder  =
      match e with
      | Const'(s)-> tbl@(adder e tbl)
      | Var'(VarFree v) -> tbl@(adder e tbl)
      | BoxSet'(_,e) -> get_tbl e tbl adder
      | If'(test, dit, dif)-> map_flat (fun e -> get_tbl e tbl adder) [test; dit; dif]
      | (Seq'(l) | Or'(l)) -> map_flat (fun e -> get_tbl e tbl adder) l
      | (Set'(_, e) | Def'(_, e)) ->  get_tbl e tbl adder
      | LambdaSimple'(_, body) -> get_tbl body tbl adder
      | LambdaOpt'(_, _, body) -> get_tbl body tbl adder
      | (Applic'(first, sexprs) | ApplicTP'(first, sexprs)) -> map_flat (fun e -> get_tbl e tbl adder) (first::sexprs)
      | _ -> []
    
      and map_flat f lst = List.flatten (List.map f lst)


  let rec add_to_const_tbl expr tbl =
      match expr with
      | Char(c) ->  append_to_set (Sexpr(expr), (next_const_offset 2, "MAKE_LITERAL_CHAR("^(string_of_int (Char.code c))^")"))  tbl
      | Number(Float f) -> append_to_set (Sexpr(expr),(next_const_offset 9, "MAKE_LITERAL_FLOAT("^(string_of_float f)^")"))  tbl
      | Number(Fraction (n, d)) -> append_to_set (Sexpr(expr),(next_const_offset 17, "MAKE_LITERAL_RATIONAL("^string_of_int n^","^string_of_int d^")"))  tbl
      | String(s) ->  append_to_set (Sexpr(expr),((next_const_offset ((String.length s) + 9), "MAKE_LITERAL_STRING \""^(String.escaped s)^"\"")))  tbl
      | Symbol(s) ->  append_to_set (Sexpr(expr),(next_const_offset 9,"MAKE_LITERAL_SYMBOL(const_tbl+"^(idx_as_str expr tbl)^")"))  tbl
      | Pair(car, cdr) ->  (let n_tbl = (add_to_const_tbl car (add_to_const_tbl cdr tbl)) in 
                            append_to_set (Sexpr(expr),(next_const_offset 17,"MAKE_LITERAL_PAIR(const_tbl+"^(idx_as_str car n_tbl)^",const_tbl+"^(idx_as_str cdr n_tbl)^")"))  n_tbl)
      | _ -> []

    and idx_as_str expr tbl = (string_of_int (fst (List.assoc expr tbl)))
    and append_to_set (a,(b,c)) tbl = if (List.mem_assoc a tbl) then tbl else  ((a,(b,c)) :: tbl) 
  
  let const_tbl_adder e tbl = 
    match e with 
    | Const'(Sexpr(expr)) -> add_to_const_tbl expr tbl
    | _ -> []

 
  let consts_tbl_init = 
    [ (Void, (next_const_offset 1, "MAKE_VOID")); 
      (Sexpr (Nil), (next_const_offset 1, "MAKE_NIL")); 
      (Sexpr(Bool false), (next_const_offset 2, "MAKE_BOOL(0)")); 
      (Sexpr(Bool true), (next_const_offset 2,"MAKE_BOOL(1)")); 
    ]
  
  let make_consts_tbl asts =  List.fold_left (fun tbl e -> get_tbl e tbl const_tbl_adder) consts_tbl_init asts;;
  
    
  let make_fvars_tbl asts = List.map (fun a -> (a, fvar_next_offset)) primitive_fvar_table;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;


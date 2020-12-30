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

  let primitive_fvar_table =  [
                                (* Type queries  *)
                                ("boolean?", 0); ("flonum?", 0); ("rational?", 0);
                                ("pair?", 0); ("null?", 0); ("char?",0); ("string?", 0); 
                                ("procedure?", 0); ("symbol?", 0); 
                                (* String procedures *)
                                ("string-length", 0); ("string-ref", 0); ("string-set!",0); ("make-string", 0); ("symbol->string",0); 
                                (* Type conversions *)
                                ("char->integer", 0); ("integer->char", 0); ("exact->inexact", 0);
                                (* Identity test *)
                                ("eq?", 0); 
                                (* Arithmetic ops *)
                                ("+", 0); ("*", 0); ("/", 0); ("=", 0); ("<", 0); 
                                (* Additional rational numebr ops *)
                                ("numerator", 0); ("denominator", 0); ("gcd", 0); 
                                (* you can add yours here *)
                                ("apply",0); ("car",0);("cdr",0); ("cons",0); ("set-car!",0); ("set-cdr!",0);
                              ]                          


  let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;


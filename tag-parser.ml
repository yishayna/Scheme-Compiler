#use "reader.ml";;
open PC;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec tag_parse sexp =
  match sexp with 
  | Bool(exp) -> Const(Sexpr(sexp))
  | Char(exp) -> Const(Sexpr(sexp))
  | Number(exp) -> Const(Sexpr(sexp))
  | String(exp) -> Const(Sexpr(sexp))
  | Symbol(sexp) -> Var((unreserved_word sexp)) 
  | Pair(Symbol("quote"),Pair(sexp,Nil)) -> Const(Sexpr(sexp))
  | Pair(Symbol("unquote"),Pair(sexp,Nil)) -> Const(Sexpr(sexp))
  | Pair(Symbol("if"),Pair(test,Pair(dit,Pair(dif,Nil)))) -> If(tag_parse test,tag_parse dit,tag_parse dif)
  | Pair(Symbol("if"),Pair(test,Pair(dit,Nil))) -> If(tag_parse test,tag_parse dit,Const(Void))
  | Pair(Symbol("cond"),ribs) -> tag_parse (cond_macro_expand ribs)
  | Pair(Symbol("lambda"),Pair(Nil,body)) -> LambdaSimple([], tag_parse_implicit body)
  | Pair(Symbol("lambda"),Pair(args,body)) -> (parse_tag_lambda args body) 
  | Pair(Symbol("or"),Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"),Pair(exp,Nil)) -> (tag_parse exp)
  | Pair(Symbol("or"),sexps) -> Or(str_to_sexps_list sexps)
  | Pair(Symbol("define"),Pair(Symbol(name),Pair(body,Nil))) -> Def(Var(unreserved_word(name)), tag_parse body)
  | Pair(Symbol("define"),Pair(Pair(name,argl),exprs)) -> tag_parse (Pair(Symbol("define"),Pair(name,Pair(Pair(Symbol("lambda"),Pair(argl,exprs)),Nil))))
  | Pair(Symbol("set!"),Pair(Symbol(name),Pair(body,Nil))) -> Set(Var(unreserved_word(name)), tag_parse body)
  | Pair(Symbol("begin"),Nil) -> Const(Void)
  | Pair(Symbol("begin"),Pair(exp,Nil)) -> (tag_parse exp)
  | Pair(Symbol("begin"),sexps) -> Seq(str_to_sexps_flatten_list sexps)
  | Pair(Symbol("let"), Pair(bindings,sexps)) -> tag_parse (let_macro_expand bindings sexps )
  | Pair(Symbol("let*"),Pair(Nil,sexps)) -> (tag_parse (Pair(Symbol("let"), Pair(Nil,sexps)))) 
  | Pair(Symbol("let*"),Pair(Pair(bindings,Nil),sexps)) -> (tag_parse (Pair(Symbol("let"), Pair(Pair(bindings,Nil) ,sexps))))    
  | Pair(Symbol("let*"),Pair(bindings,sexps)) -> (tag_parse (let_klenee_macro_expand bindings sexps))
  | Pair(Symbol("letrec"), Pair(bindings,sexps)) -> tag_parse (letrec_macro_expand bindings sexps)
  | Pair(Symbol("quasiquote"),Pair(sexp,Nil)) -> tag_parse (quasiquote_macro_expand sexp)
  | Pair(Symbol("and"),Nil) -> Const(Sexpr(Bool(true)))
  | Pair(Symbol("and"),Pair(exp,Nil)) -> tag_parse exp
  | Pair(Symbol("and"),exp) -> tag_parse (and_macro_expand exp)
  | Pair(Symbol("pset!"),exps) -> tag_parse (pset_macro_expand exps)
  | Pair(first,rest) -> Applic( tag_parse first, str_to_sexps_list rest)
  | _ -> raise (X_syntax_error)

  (*Go through Pairs and activate parse on each var while creating a list*)
  and split_sexps_list parser sexps = 
  let rec split sexps= 
    match sexps with
    | Pair(x,Nil) -> (parser x)
    | Pair(x,y) -> List.append (parser x) (split y)
    | Nil -> []
    | _ -> raise (X_no_match) in
  (split sexps)


  and parse_tag_seq expr =  
    let x = tag_parse expr in
      match x with
      | Seq(a) -> a
      | _ ->  [x]


  and parse_tag_lambda args body =
  match args with
  | Symbol(args) -> LambdaOpt([],args,tag_parse_implicit body)
  | _ -> (
    let parsed_args =  parse_args args in
    let body = tag_parse_implicit body in
    if (is_proper_args args) 
    then LambdaSimple(parsed_args, body) 
    else LambdaOpt((args_without_opt parsed_args),(opt_var parsed_args),body))

(*Helper checks for lambda*)

and parse_valid_arg sexps =
  let rec split sexps = 
    match sexps with
    | Pair(Symbol(x),Nil) -> [x]
    | Pair(Symbol(x),Symbol(y)) -> [x;y]
    | Pair(Symbol(x),y) -> List.append [x] (split y)
    | Nil -> []
    | _ -> raise (X_no_match) in
    let lst = (split sexps) in
    if (duplicates_exists lst) then raise (X_no_match) else lst



and is_proper_args s = 
  let rec is_proper s =
    match s with 
    | Pair(x,Nil) -> true
    | Pair(x,y) ->  (is_proper y)
    | _ -> false in
  (is_proper s)

  and opt_var lst = (List.hd (List.rev lst))
  and args_without_opt lst = (List.rev (List.tl (List.rev lst))) 

  

  and parse_tag_list expr =  [tag_parse expr] 
  and str_to_sexps_list sexps = (split_sexps_list parse_tag_list sexps)
  and str_to_sexps_flatten_list sexps = (split_sexps_list parse_tag_seq sexps)
  and parse_args sexps = (parse_valid_arg sexps)

 

  and duplicates_exists lst =
    let rec contains  = function 
      | []  -> false
      | hd::t1 -> List.exists ( (=) hd) t1 || contains t1 in
    (contains lst)


  and unreserved_word word = if (List.mem word reserved_word_list) then raise(X_syntax_error) else word 
  and unreserved_string str = (List.map unreserved_word str)  


  and tag_parse_implicit sexp = 
    match sexp with
    | Pair(x,Nil) -> (tag_parse x)
    | Pair(x,y) -> Seq(str_to_sexps_flatten_list sexp )
    | _ -> raise (X_no_match)   (* need to think about it!*)


  
  and get_bindings_ref  bindings = 
    let rec split bindings = 
      match bindings with
      | Pair (Pair(Symbol(x),Pair(y,Nil)), s) -> Pair(Symbol(unreserved_word x),(split s))      
      | Nil -> Nil
      | _ -> raise (X_no_match) in
    (split bindings)
  
  
  and get_bindings_values bindings = 
    let rec split bindings = 
      match bindings with
      | Pair(Pair(Symbol(x),Pair(y,Nil)), s) -> Pair(y,(split s))      
      | Nil -> Nil
      | _ -> raise (X_no_match) in
    (split bindings)
    
  
  and let_macro_expand bindings sexps = 
    let bindings_ref =  get_bindings_ref bindings in
    let bindings_values =  get_bindings_values bindings in
    Pair(Pair(Symbol("lambda"),Pair(bindings_ref,sexps)),bindings_values)


  and let_klenee_macro_expand bindings sexps = 
      match bindings with
      | Pair(first,rest)  ->  
        Pair(Symbol("let"), Pair(Pair(first,Nil), Pair(Pair(Symbol("let*"),Pair(rest,sexps)), Nil)))     
      | _ -> raise (X_no_match)           
 
  and get_new_bindings  sexps = 
    let rec split sexps= 
      match sexps with
      | Pair(Pair(Symbol(x),y), s) -> x::(split s)   
      | Nil -> []
      | _ -> raise (X_no_match) in
    (split sexps)

  and make_bindings  lst  = 
    let rec split lst = 
      match lst with
      | (x :: s) -> Pair(Symbol(x), split s)
      | [] -> Nil in 
    (split lst)
  
  and make_uniqe_args lst =
    let rec get_uniqe_dollar hd n_lst = 
      let n_hd = "$"^hd in
      if ((List.mem n_hd n_lst) || (List.mem n_hd lst ))  then (get_uniqe_dollar n_hd n_lst) else  n_hd:: n_lst in
    (List.fold_right (fun a acc -> (get_uniqe_dollar a acc )) lst [] )
    
  and get_new_body lst_old lst_new = 
    let rec split lst_old lst_new = 
      match lst_old with
      | (x :: s) -> Pair(Pair(Symbol("set!"),Pair(Symbol(x),Pair(Symbol(List.hd lst_new),Nil))),split s (List.tl lst_new))
      | [] -> Nil in
    (split lst_old lst_new)
  
  and pset_macro_expand sexps = 
    let bindings_ref =  get_new_bindings sexps in
    let uniqe_args =  (make_uniqe_args bindings_ref) in
    let args = make_bindings uniqe_args in
    let body = get_new_body bindings_ref uniqe_args in    
    let values = get_bindings_values sexps in 
    Pair(Pair(Symbol("lambda"),Pair(args, body)),values)
 
 

   


    
    
  and split_sexps_pairs parser sexps = 
    let rec split sexps= 
      match sexps with
      | Pair(x,y) -> Pair((parser x),split y)
      | Nil -> Nil
      | _ -> raise (X_no_match) in
    (split sexps)

  
  and get_bindings_with_set bindings sexp = 
    let rec split bindings sexp = 
      match bindings with
      | Pair(Pair(x,y), s) -> Pair(Pair(Symbol("set!"), Pair(x,y)) ,(split s sexp))
      | Nil -> Pair(Pair(Symbol("let"),Pair(Nil,sexp)),Nil)
      | _ -> raise (X_no_match) in
    (split bindings sexp)



  and letrec_macro_expand bindings sexps = 
    let bindings_ref =  get_bindings_ref bindings in
    let quasi_w  x = Pair(x ,Pair(Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil)),Nil)) in
    let first = (split_sexps_pairs quasi_w bindings_ref) in
    let second = get_bindings_with_set bindings sexps in
    Pair(Symbol("let"),Pair(first, second))


  and and_macro_expand exp = 
    let rec tag_parse_and exp = 
      match exp with 
      | Pair(exp,Pair(rest,Nil)) -> 
            Pair(Symbol("if"),
              Pair(exp,
                Pair(rest,
                  Pair(Bool(false),Nil))))
      | Pair(exp,rest) ->
            Pair(Symbol("if"),
              Pair(exp,
                Pair(and_macro_expand rest,
                  Pair(Bool(false),Nil))))
      | _ -> raise X_syntax_error in
    (tag_parse_and exp)
  



  and cond_macro_expand ribs = 
  match ribs with 
  | Pair(Pair(exp,Pair(Symbol("=>"),Pair(rest,Nil))),Nil) -> 
      Pair(Symbol("let"),Pair(Pair(Pair(Symbol("value"),Pair(exp,Nil)),
      Pair(Pair(Symbol("f"),Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(rest,Nil))),Nil)),Nil)),
      Pair(Pair(Symbol("if"),Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"),Nil),
      Pair(Symbol("value"),Nil)),Nil))),Nil)))
  | Pair(Pair(exp,Pair(Symbol("=>"),exprf)),rest) ->
      Pair(Symbol("let"),Pair(Pair(Pair(Symbol("value"),Pair(exp,Nil)),
      Pair(Pair(Symbol("f"),Pair(Pair(Symbol("lambda"),Pair(Nil,exprf)),Nil)),
      Pair(Pair(Symbol("rest"),Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(cond_macro_expand rest,Nil))),Nil)),Nil))),
      Pair(Pair(Symbol("if"),Pair(Symbol("value"),Pair(Pair(Pair(Symbol("f"),Nil),Pair(Symbol("value"),Nil)),
      Pair(Pair(Symbol("rest"),Nil),Nil)))),Nil)))
  | Pair(Pair(Symbol("else"),rest),_) -> Pair(Symbol("begin"),rest)
  | Pair(Pair(rib,body),Nil) -> Pair(Symbol("if"),Pair(rib,Pair(Pair(Symbol("begin"),body),Nil)))
  | Pair(Pair(rib,body),rest) -> Pair(Symbol("if"),Pair(rib,Pair(Pair(Symbol("begin"),body),Pair((cond_macro_expand rest),Nil))))
  | _ -> raise X_syntax_error  



and quasiquote_macro_expand sexp = 
  match sexp with
  | Pair(Symbol("unquote"),Pair(sexp,Nil)) -> sexp
  | Pair(Symbol("unquote-splicing"),Pair(sexp,Nil)) -> raise X_syntax_error
  | Nil -> Pair(Symbol("quote"),Pair(sexp,Nil)) 
  | Symbol(exp) -> Pair(Symbol("quote"),Pair(sexp,Nil)) 
  | Pair(car,cdr) -> (match (car,cdr) with
    | (Pair(Symbol("unquote-splicing"),Pair(car,_)),cdr) -> Pair(Symbol("append"),Pair(car,Pair(quasiquote_macro_expand cdr,Nil)))
    | (car,Pair(Symbol("unquote-splicing"),Pair(cdr,_))) -> Pair(Symbol("cons"),Pair(quasiquote_macro_expand car,Pair(cdr,Nil)))
    | _ -> Pair(Symbol("cons"),Pair(quasiquote_macro_expand car,Pair(quasiquote_macro_expand cdr,Nil))))
  | _ -> raise X_syntax_error




let tag_parse_expressions sexpr = List.map tag_parse sexpr;;


  
end;; (* struct Tag_Parser *)




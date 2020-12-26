#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let seq_id = ref 0 ;;
let next_seq_id() = let v= !seq_id in
  (seq_id:= v+1 ; !seq_id);;
let init_seq_id() = (seq_id:= 0 ; !seq_id);;

let lamb_id = ref 1 ;;
let next_lamb_id() = let v= !lamb_id in
  (lamb_id:= v+1 ; !lamb_id);;
let init_lamb_id() = (lamb_id:= 1 ; !lamb_id);;


let get_var_idx lst v =
  let rec get_idx lst v =
    match lst with 
    | [] -> raise X_no_match
    | hd :: tl -> if v = hd then 0 else 1 + (get_idx tl v)  in
  (get_idx lst v) 


let rec annotate_lexical bound_lst param_lst expr =
  let make_expr' =  annotate_lexical bound_lst param_lst in
  let make_var'  = make_var_lexical bound_lst param_lst in
    match expr with 
    | Const(s)->Const'(s)
    | Var(v)->Var'(make_var' v)
    | If(test,dit,dif)-> If'((make_expr' test),(make_expr' dit),(make_expr' dif))
    | Seq(sexprs) -> Seq'(List.map make_expr' sexprs)
    | Set(Var(v),value)-> Set'((make_var' v),(make_expr' value)) 
    | Def(Var(v),value)->Def'((make_var' v),(make_expr' value))
    | Or(sexprs) ->Or'(List.map make_expr' sexprs)
    | Applic(first,sexprs) -> Applic' ((make_expr' first),(List.map make_expr' sexprs))
    | LambdaSimple (args,body)-> LambdaSimple'(args, annotate_lexical (args::bound_lst) args body)
    | LambdaOpt(args,opt,body)-> LambdaOpt'(args,opt, annotate_lexical ((args@[opt])::bound_lst) (args@[opt]) body) 
    | _ -> raise X_syntax_error 


  and make_var_lexical bound_lst param_lst v =
    try VarParam(v,get_var_idx param_lst v)
    with X_no_match ->  
    try let (major,minor) = get_lst_idx (List.tl bound_lst) v in  VarBound(v,major,minor)
    with _ ->  VarFree(v)


  and get_lst_idx lists v =
    let rec get_idx lists v =
      match lists with 
      | [] -> raise X_no_match
      | hd :: tl -> if List.mem v hd then (0,get_var_idx hd v) else (let (major,minor) = get_idx tl v in (1+ major, minor)) in
      (get_idx lists v)


let rec annotate_tail tp expr=
  match expr with 
    | Set'(v,value)-> Set'(v, annotate_tail false value)
    | Def'(v,value)-> Def'(v, annotate_tail false value)
    | Or'(sexprs) ->Or'(annotate_tail_rest tp sexprs)
    | Seq'(sexprs) -> Seq'(annotate_tail_rest tp sexprs)
    | Applic'(first,sexprs) when tp = true -> ApplicTP'(annotate_tail false first, List.map (annotate_tail false) sexprs)
    | Applic'(first,sexprs) when tp = false -> Applic'(annotate_tail false first, List.map (annotate_tail false) sexprs) 
    | If'(test,dit,dif)-> If'((annotate_tail false test) ,(annotate_tail tp dit),(annotate_tail tp dif))
    | LambdaSimple' (args,body)-> LambdaSimple'(args, annotate_tail true body)
    | LambdaOpt'(args,opt,body)-> LambdaOpt'(args, opt, annotate_tail true body)
    | _ -> expr
  
  and annotate_tail_rest tp sexprs =  
    let rev_lst =  (List.rev sexprs) in
    (List.map (annotate_tail false) (List.rev (List.tl rev_lst)))@[(annotate_tail tp (List.hd rev_lst))]
  

let rec set_boxes vars expr  =
  let set_box_rec = set_boxes vars in  
  match expr with 
    | Or'(sexprs) ->Or'(List.map set_box_rec  sexprs)
    | Seq'(sexprs) -> Seq'(List.map set_box_rec  sexprs)
    | Applic'(first,sexprs) -> Applic'(set_box_rec first, List.map set_box_rec  sexprs)
    | ApplicTP'(first,sexprs) -> ApplicTP'(set_box_rec first, List.map set_box_rec  sexprs)
    | If'(test,dit,dif)-> If'((set_box_rec  test) ,(set_box_rec dit),(set_box_rec dif)) 
    | Var'(v) when List.mem v vars -> BoxGet'(v) 
    | Set'(v,value)->  if List.mem v vars then BoxSet'(v, set_box_rec value) else Set'(v , set_box_rec value)
    | Def'(v,value)->  if List.mem v vars then BoxSet'(v, set_box_rec value) else Def'(v , set_box_rec value)
    | LambdaSimple' (args,body)->  set_boxes_lambda args [] body vars 
    | LambdaOpt'(args,opt,body)-> set_boxes_lambda args [opt] body vars 
    | _ -> expr

  and map_flat f lst = List.flatten (List.map f lst)

  and read_write e lst lamb_id seq_id body = 
    let read_write_rec =  read_write e lst lamb_id seq_id  in 
    let read_write_rec_lambda _lamb_id = read_write e lst _lamb_id seq_id in 
     match body with
      | Var'(VarBound(v,major,minor)) when v = e  -> lst@[("r",lamb_id,seq_id,(-1))]
      | Var'(VarParam (v,mn)) when v = e  -> lst@[("r",lamb_id,seq_id,(-1))]
      | If'(test,dit,dif)-> lst@(map_flat read_write_rec [test;dit;dif]) 
      | Seq'(sexprs) -> let _seq_id = next_seq_id() in lst@(List.map (fun (a,b,c,d) -> (a,b,c,(b-lamb_id))) (map_flat (read_write e lst lamb_id _seq_id) sexprs))  
      | Set'(v, value) -> lst@(read_write_rec value)@(check_write_var v e lamb_id seq_id)
      | Def'(v, value) -> lst@(read_write_rec value)@(check_write_var v e lamb_id seq_id)
      | Or'(sexprs) -> lst@(map_flat read_write_rec sexprs)
      | Applic'(first,sexprs) ->  lst@(map_flat read_write_rec (first::sexprs)) 
      | ApplicTP'(first,sexprs) ->  lst@(map_flat read_write_rec (first::sexprs)) 
      | LambdaSimple'(args,body) ->   if (List.mem e args) then lst else let _lamb_id = next_lamb_id() in  lst@((read_write_rec_lambda _lamb_id) body)
      | LambdaOpt'(args,opt,body) ->   if (List.mem e args) then lst else let _lamb_id = next_lamb_id() in lst@((read_write_rec_lambda _lamb_id) body)
      | _ -> lst


    and find_occur lst (t,lamb_id,seq_id,rel_depth_seq) =
    let rec find lst =
      match lst with 
      | [] -> false 
      | ((t_curr,lamb_id_curr,seq_id_curr,rel_depth_seq_curr)::tl) when ((t_curr = t) && (rel_depth_seq_curr!= 0) && (rel_depth_seq = 0) && (seq_id_curr = seq_id)) ->  false || (find (List.tl lst)) 
      | ((t_curr,lamb_id_curr,seq_id_curr,rel_depth_seq_curr)::tl) when ((t_curr = t) && (lamb_id_curr != lamb_id)) ->  true
      |_ -> (find (List.tl lst)) in
    (find lst)

    and get_rw_value lst = 
    let rec get_rw lst =
      match lst with 
      | [] -> false
      | ((t,lamb_id,seq_id,rel_depth_seq)::tl) when t = "r" -> (find_occur tl ("w",lamb_id,seq_id,rel_depth_seq)) || (get_rw tl)
      | ((t,lamb_id,seq_id,rel_depth_seq)::tl) when t = "w" -> (find_occur tl ("r",lamb_id,seq_id,rel_depth_seq)) || (get_rw tl) 
      |_ -> raise X_syntax_error in
    (get_rw lst)

  and check_write_var v e lamb_id seq_id=
    match v with 
      | VarFree (v) when (v = e) -> [("w",lamb_id,seq_id, (-1))]
      | VarParam (v,mn) when (v = e) -> [("w",lamb_id,seq_id, (-1))]
      | VarBound (v,major,minor) when (v = e) -> [("w",lamb_id,seq_id,(-1))]
      |_ -> []

  and seq_flat expr' =  
      match expr' with
      | Seq'(a) -> a
      | _ ->  [expr']
  
  and update_dist v =
    match v with 
    |  VarParam(v, idx) -> VarBound(v,0,idx)
    |  VarBound(v,major,minor) -> VarBound(v,major+1,minor)
    | _ ->  v

  and set_boxes_lambda args opt body vars  = 
    let m_args = args@opt in
    let set_rw e = let _lamb_id = init_lamb_id() in let _seq_id = init_seq_id() in (e,  get_rw_value (read_write e [] _lamb_id _seq_id body)) in
    let args' = List.map (fun (e,b) -> e) (List.filter (fun (e,rw) -> rw) (List.map set_rw m_args)) in
    let params_lst = if m_args = [] then [] else List.map (fun v ->  VarParam (v,get_var_idx m_args v)) args' in
    let vars = params_lst@(List.map update_dist vars) in
    let body_lst =  List.flatten (List.map seq_flat ((List.map (fun v -> Set'(v,Box'(v))) params_lst)@[set_boxes vars body])) in
    let body = if List.length body_lst = 1 then  (List.hd body_lst) else Seq'(body_lst) in
    if opt = [] then  LambdaSimple' (args, body) else LambdaOpt'(args, (List.hd opt), body)


let annotate_lexical_addresses e = annotate_lexical [] [] e;;

let annotate_tail_calls e = annotate_tail false e ;;

let box_set e =  set_boxes [] e;;

let run_semantics expr =
  box_set 
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)



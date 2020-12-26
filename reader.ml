
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

(* We copied the following functions from the practical session's materials.*)

  let make_paired nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_ ,e) -> e)  in
    let nt = caten nt nt_right  in
    let nt = pack nt (function (e, _) -> e)  in
    nt;;

  let make_spaced nt =  make_paired (star nt_whitespace)  (star nt_whitespace) nt;;
  let tok_lparen = make_spaced  (char '(') ;;
  let tok_rparen = make_spaced  (char ')') ;;

(*end*)

  let digit = range '0' '9';;
  let natural_number = star digit;;

  let digit_to_natural_val c = ((int_of_char c) - (int_of_char '0'));; 
  let digit_to_float_val c = float_of_int (digit_to_natural_val c);; 
  let rec gcd a b = if b = 0 then a else gcd b (a mod b);;

  let char_nul = char_of_int 0 ;;  
  let char_tab = char_of_int 9 ;;  
  let char_newline = char_of_int 10 ;; 
  let char_page = char_of_int 12 ;; 
  let char_return = char_of_int 13 ;;
  let char_spaced = char_of_int 32 ;; 
  let char_double_quote = char_of_int 34 ;;
  let char_quote = char_of_int 39 ;; 
  let char_unquote = char_of_int 44 ;; 
  let char_backslash = char_of_int 92 ;; 
  let char_quasiquote = char_of_int 96 ;; 

  let range_ci_to_lower = pack (range_ci 'a' 'z') (fun a -> lowercase_ascii a)
  let char_no_dot = disj_list [digit; range_ci_to_lower; (one_of "!$^*-_=+<>?/:")] ;;
  let dot = (char '.');;
  let symbol_char = disj char_no_dot dot ;;
  

  let rec nt_expr input = 

    let parse = disj_list [parse_bool;parse_char;parse_float;parse_fraction;parse_string;parse_symbol;parse_empty_list;parse_list;parse__dotted_list;parse_quote_forms] in
    skip parse input
  
    and sexpr_comments input = 
      let start = (word "#;") in
      let nt = caten start nt_expr in
      let nt = pack nt (fun (a,b) -> ()) in
      nt input
  
    and line_comments input = 
      let start = (char ';') in
      let end_line = disj (pack nt_end_of_input (fun _ -> ())) (pack (char '\n') (fun _ -> ())) in
      let nt = diff nt_any end_line in
      let nt = caten start (star nt) in
      let nt = pack nt (fun (a,b) -> ()) in   
      nt input
  
    and parse_whitespaces input = 
      (pack nt_whitespace (fun _ -> ())) input
  
  
    and nt_skip input = 
      let comments = disj line_comments sexpr_comments in
      let skip = disj parse_whitespaces comments in  
      skip input
  
    and skip nt input =
      let skip_rec = star nt_skip in
      ((make_paired skip_rec skip_rec) nt) input
  

    and parse_symbol input =
      let nt = pack (caten symbol_char (plus symbol_char)) (fun (a,b) ->  (list_to_string (a::b))) in 
      let char_as_str = pack char_no_dot (fun (a) -> String.make 1 a) in
      let nt = disj nt char_as_str in
      let nt = pack nt (fun (a)->Symbol(a)) in
      nt input


    and sign_of_int a = if a<0 then -1. else 1.

    and parse_sign input = 
      let minus = pack (char '-') (fun _ -> -1 ) in
      let plus = pack (char '+') (fun _ -> 1 ) in
      let if_sign = maybe (disj minus plus) in
      let ret_sign = pack if_sign (function
        None -> 1 
        | Some(x) -> x) in
      ret_sign input

    and natural_str_to_value ls = 
      List.fold_left (fun u x -> u*10 + (digit_to_natural_val x)) 0 ls

    and float_str_to_value ls = 
      List.fold_right (fun x u -> u/.10. +. (digit_to_float_val x)/.10.) ls 0.

    and parse_natural_num str =
      let nt = pack (plus digit) natural_str_to_value in 
      nt str

    and parse_float_num str =
      let nt = pack (plus digit) float_str_to_value in
      nt str

    and parse_num_sign input = 
      let nt = caten parse_sign parse_natural_num in
      let nt = pack nt (fun (sign,number) -> (sign * number,sign)) in
      nt input

    and parse_num input = 
      let nt = pack parse_num_sign (fun (sigend_num,sign) -> sigend_num) in
      nt input

    and parse_integer_value input = 
      let nt = pack parse_num (fun (a) ->  (a,1)) in
      nt input 
    
    
    and parse_fraction_value input = 
      let nt1 = caten parse_num (char '/') in
      let nt2 = caten nt1 parse_natural_num in
      let nt = pack nt2 (function ((a,b),c) ->  
      let gcd_div =  (gcd a c)  in
      let div = if gcd_div = 0 then 1 else (abs gcd_div) in
      (a/div,c/div)) in 
      nt input 
    
    and parse_float_value input = 
      let nt1 = caten parse_num_sign (char '.') in
      let nt2 = caten nt1 parse_float_num in
      let nt = pack nt2 (fun (((sigend_num,sign),b),c) -> ((float_of_int sigend_num) +. c*. (float_of_int sign))) in 
      nt input 

    and parse_scientific input = 
      let parse_fraction_as_float = pack parse_integer_value  (fun (a,b) -> (float_of_int (a/b)))  in
      let parse_numbers = disj parse_float_value parse_fraction_as_float  in
      let nt = caten parse_numbers (char_ci 'e') in
      let nt = caten nt parse_num in
      let nt = pack nt (fun ((value,b),exponent) -> value *.10.** (float_of_int exponent)) in 
      nt input  

    and parse_fraction input = 
      let nt  =  disj parse_fraction_value parse_integer_value  in
      let nt = not_followed_by nt symbol_char in
      let nt  = pack nt (fun (a,b) ->  Number(Fraction(a,b))) in 
      nt input
    
    
    and parse_float input = 
      let nt  = disj  parse_scientific parse_float_value   in
      let nt = not_followed_by nt symbol_char in
      let nt = pack nt (fun (a) ->  Number(Float(a))) in 
      nt input 
      
     
    and parse_bool input = 
      let nt_t = pack (word_ci "#t") (fun x -> Bool(true)) in
      let nt_f = pack (word_ci "#f") (fun x -> Bool(false)) in
      let nt = disj nt_t nt_f in
      nt input

    and parse_string input = 
        (* A special backslash must precede Meta Chars. we need to remove the extra backslash while parsing into ASTs*)
        let nt_return = pack (word_ci "\\r") (fun _ -> char_return) in
        let nt_newline = pack (word_ci "\\n") (fun _ -> char_newline) in
        let nt_tab = pack (word_ci "\\t") (fun _ -> char_tab) in
        let nt_page = pack (word_ci "\\f") (fun _ -> char_page) in
        let nt_backslash = pack (word_ci "\\\\") (fun _ -> char_backslash) in
        let nt_double_quote = pack (word_ci "\\\"") (fun _ -> char_double_quote) in
        
        let literal_chars = const (fun (ch) -> match ch with 
            | '\"' -> false
            | '\\' -> false
            | _ -> true) in 

        let nt_literal_chars = pack literal_chars (fun e -> e) in
        let nt_meta_chars = disj_list [nt_return;nt_newline;nt_tab;nt_page;nt_backslash;nt_double_quote] in
        let nt = disj nt_literal_chars nt_meta_chars in 
        
        (* A string must be surrounded with the double quote char*)
        let nt = make_paired (char '\"') (char '\"') (star nt) in    
        let nt = pack nt (fun s -> String(list_to_string s)) in 
        nt input

    and parse_char input = 
      let nt_nul = pack (word_ci "nul") (fun _ -> char_nul) in
      let nt_newline = pack (word_ci "newline") (fun _ -> char_newline) in
      let nt_return = pack (word_ci "return") (fun _ -> char_return) in
      let nt_tab = pack (word_ci "tab") (fun _ -> char_tab) in
      let nt_page = pack (word_ci "page") (fun _ -> char_page) in
      let nt_spaced = pack (word_ci "space") (fun _ -> char_spaced) in
      
      let nt_named_chars = disj_list [nt_nul;nt_newline;nt_return;nt_tab;nt_page;nt_spaced] in
      let nt_visible_chars =  const (fun (ch) -> ch > char_spaced) in
      let nt_chars = disj nt_named_chars nt_visible_chars in
      let nt_char_prefix =  word_ci "#\\" in
      let nt = caten nt_char_prefix nt_chars in
      let nt = pack nt (fun (e,s) -> Char s) in
      nt input

    and parse_empty_list input =
      let nt = caten (caten tok_lparen (star nt_skip)) tok_rparen  in
      let nt = pack nt (fun _ -> Nil) in   
      nt input
    
    and parse_quote_forms input =
      let nt_quote = pack (caten (char_ci char_quote) nt_expr) (fun (_,s) -> ("quote",s)) in
      let nt_quasiquote = pack (caten (char_ci char_quasiquote) nt_expr) (fun (_,s) -> "quasiquote",s) in
      let nt_unquote = pack (caten (char_ci char_unquote) nt_expr) (fun (_,s) -> "unquote",s) in
      let nt_unquote_splicing = pack (caten (word_ci ",@")  nt_expr) (fun (_,s) -> "unquote-splicing",s) in
      let nt_quote_forms = disj_list [nt_quote;nt_quasiquote;nt_unquote;nt_unquote_splicing] in
      let nt = pack nt_quote_forms (fun (a,s) -> Pair(Symbol(a),Pair(s,Nil))) in
      nt input


    and parse_list input =
      let nt = caten (caten tok_lparen (star nt_expr)) tok_rparen in
      let nt = pack nt (fun ((l,exp_list),r) -> List.fold_right (fun a b -> Pair(a,b)) exp_list Nil ) in
      nt input

    and parse__dotted_list input =
      let nt = pack (caten tok_lparen (plus nt_expr)) (fun (l,exp) -> exp) in
      let nt = pack (caten nt (char '.')) (fun (exp1,dot) -> exp1) in
      let nt = pack (caten nt  nt_expr) (fun (exp1,exp2) -> (exp1,exp2)) in
      let nt = pack (caten nt tok_rparen) (fun ((exp1,exp2),r) -> (exp1,exp2)) in
      let nt = pack nt (fun (exp1,exp2) -> List.fold_right (fun a b -> Pair(a,b)) exp1 exp2) in
      nt input

let rec sexprs_runner lst =
  if lst = [] then []
  else 
    let (e,s) = nt_expr lst in
    e :: (sexprs_runner s);;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;



let read_sexprs string =  
  sexprs_runner (string_to_list string);;


end;; (* struct Reader *)

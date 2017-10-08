open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open stringLib  
open pairTheory  
open numLib
open numTheory
open ratTheory
open bossLib
open fracTheory 
open listLib 
open satTheory
open sortingTheory  
open relationTheory
 
val _ = Hol_datatype ` Cand = cand of string ` ; 

val _ = Hol_datatype `judgement =  
                                      state   of 
                         ((Cand list) # (int # int)) list
                                             # (Cand # (int # int)) list
                                             # (Cand # (((Cand list) # (int # int)) list)) list
                                             # Cand list 
                                             # Cand list
                                             # Cand list 
                       | winners of (Cand list) `; 

(* start of first part *)
val cand_list =
 fn str =>
       let val lst = String.explode str
           fun t_cand_list tlst = 
             case tlst of 
                 [] => []
               | (#"," :: t) => t_cand_list t
               | (#"[" :: t) => t_cand_list t
               | (#"]" :: t) => t_cand_list t
               | (#" " :: t) => t_cand_list t
               | (x :: t) => Cand (String.str x) :: t_cand_list t
       in t_cand_list lst 
       end 
           
           
val split_it_into_pair = 
 fn str => 
    let val ltm = String.explode str 
        fun process_chunk tlst acc lst = 
          case  (tlst, acc, lst) of
              ([], acc, lst) => lst 
            | ((#"[" :: t), acc, lst) => process_chunk t (String.concat [acc,  "["]) lst
            | ((#"(" :: t), acc, lst) => process_chunk t (String.concat [acc, "("]) lst
            | ((#")" :: #"," :: t), acc, lst) => 
              process_chunk t "" 
                            (List.concat [lst, [String.concat [acc, ")"]]])
            | ((#")" :: t), acc, lst) => 
              process_chunk t "" 
                            (List.concat [lst, [String.concat [acc, ")"]]]) 
            | ((x :: t), acc, lst)  => process_chunk t (String.concat [acc, (String.str x)]) lst
    in process_chunk (List.tl ltm) "" []
    end 

val parse_pair = 
 fn str => 
    let val tm = String.explode str 
        fun parse_t ts (ac, bc) = 
          case (ts, (ac, bc)) of
              ([], (ac, bc)) => (ac, bc)
            | ((#"(" :: t), (ac, bc)) => parse_t t (ac, bc)
            | ((#")" :: t), (ac, bc)) => parse_t t (ac, bc)
            | ((#"]" :: #"," :: t), (ac, bc)) => 
              (String.concat [ac, "]"], String.implode t)
            | ((x :: t), (ac, bc)) => 
              parse_t t (String.concat [ac, String.str x], bc)   
    in parse_t tm ("", "") 
    end 
        
(* "123" -> 123 *)
val parse_number = 
 fn str => 
    let val nlst = String.explode str
        fun t_parse_number lst acc = 
          case lst of 
              [] => acc
            | h :: t => t_parse_number t (10 * acc + (Char.ord h - Char.ord #"0"))
    in t_parse_number nlst 0
    end
        
val isDigit = 
 fn c => 
    case c of 
        #"0" => true 
      | #"1" => true
      | #"2" => true
      | #"3" => true
      | #"4" => true
      | #"5" => true
      | #"6" => true
      | #"7" => true
      | #"8" => true
      | #"9" => true       
      | _ => false  
                              
(* "a%b)" => (a, b) *)
val parse_rational = fn str => 
  let val tlst = String.tokens (fn x => x = #"%") str 
      val first = List.hd tlst
      val st = String.explode (List.hd (List.tl tlst))
      val second = String.implode (List.filter isDigit st) 
  in (parse_number first, parse_number second)
  end

(* lets plug the values togather for first part*)

val parse_first_part =
 fn str =>
    let val l1 = split_it_into_pair str
        val l2 = List.map (fn x => parse_pair x) l1
        val l3 = List.map (fn (a, b) => (cand_list a, parse_rational b)) l2
    in l3
    end
        
val first_final_part = parse_first_part "[([A,B,C],1%2),([C,B,A],1%2),([B,A,C],1%2),([C,A,B],1%2),([A,B,C],1%2),([A,B,C],1%2),([C,B,A],1%2),([A,C,B],1%2),([B,C,A],1%2),([A,B,C],3%4)]"


(* End of first part. Cakeml is getting on my nurves *)

(* start of second part *)

val parse_second_part =
    fn str =>
       let val strs = String.tokens (fn x => x = #" ") str
           fun parse_t tstr = 
             let val lstr = String.tokens (fn x => x = #"{") tstr
                 val first = List.hd lstr
                 val lrest = List.hd (List.tl lstr)
             in (Cand first, parse_rational lrest)
             end
       in List.map parse_t strs
       end

val second_final_test =  parse_second_part " A{5%6} B{2%3} C{3%4}"
                                           
(* parse_third_part *)
                                           
val parse_third_part =
    fn str =>
       let val strs = String.tokens (fn x => x = #" ") str
           fun t_parse tstr =
             let val tlst = String.tokens (fn x => x = #"{") tstr
                 val first = List.hd tlst
                 val second = List.hd (List.tl tlst)
             in (Cand first, parse_first_part second)
             end
       in List.map t_parse strs
       end
           
val third_string_s = parse_third_part " A{[([A,B,C],1%2),([A,B,C],1%2),([A,B,C],1%2),([A,C,B],1%2),([A,B,C],1%3)]} B{[([B,A,C],1%40),([B,C,A],1%2)]} C{[([C,B,A],1%2),([C,A,B],1%5),([C,B,A],15%16)]}"
                                      
(* end of third part *)
                                      
(* parse rest part, third, fourth and final *)
val parse_rest = 
    fn str => cand_list str 
                               
 (* combine all to parse one line *)

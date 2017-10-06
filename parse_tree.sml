datatype Cand = cand of string

datatype judgement =  
         state  of 
         ((Cand list) * int) list
                             * (Cand * int) list
                             * (Cand * (((Cand list) * int) list)) list
                             * Cand list 
                             * Cand list
                             * Cand list 
         | winners of (Cand list)





(* break each line at semi colon *)
(* fun top_call_split_at_semi str = String.tokens (fn x => x = #";") str *)

(* once string is split; process the each part separate *)
val f = "state [([A,B,C],1.0),([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],1.0)]"

(* This function parses "[A,B,C,D]" into [cand "A", cand "B", cand "C", cand "D"] *)
fun cand_list str = 
  let val lst = explode str 
      fun t_cand_list [] = []
        | t_cand_list (#"," :: t) = t_cand_list t
        | t_cand_list (#"[" :: t) = t_cand_list t
        | t_cand_list (#"]" :: t) = t_cand_list t
        | t_cand_list (#" " :: t) = t_cand_list t
        | t_cand_list (x :: t) = cand (String.str x) :: t_cand_list t
  in t_cand_list lst 
  end  
 
(* It will change to p / q in milad's code *)
fun parse_number n = Real.fromString n 
     
val test_cand = cand_list "[A,B,C]"
val test_number = parse_number "1.0"


fun split_it_into_pair str = 
  let val ltm = explode str 
      fun process_chunk [] acc lst = lst 
        | process_chunk (#"[" :: t) acc lst = process_chunk t (acc ^ "[") lst
        | process_chunk (#"(" :: t) acc lst = process_chunk t (acc ^ "(") lst
        | process_chunk (#")" :: #"," :: t) acc lst = process_chunk t "" (lst @ [acc ^ ")"])
        | process_chunk (#")" :: t) acc lst = process_chunk t "" (lst @[acc ^ ")"]) 
        | process_chunk (x :: t) acc lst  = process_chunk t (acc ^ String.str x) lst
  in process_chunk (tl ltm) "" []
  end    

val test_pair = split_it_into_pair "[([A,B,C],1.0),([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],3.0)]"


fun parse_pair str = 
  let val tm = explode str 
      fun parse_t [] (ac, bc) = (ac, bc)
        | parse_t (#"(" :: t) (ac, bc) = parse_t t (ac, bc)
        | parse_t (#")" :: t) (ac, bc) = parse_t t (ac, bc)
        | parse_t (#"]" :: #"," :: t) (ac, bc) = (ac ^ "]", implode t)
        | parse_t (x :: t) (ac, bc) = parse_t t (ac ^ String.str x, bc)   
  in parse_t tm ("", "") 
  end    

(* lets plug the values togather for first part*)

fun parse_first_part str = 
  let val l1 = split_it_into_pair str
      val l2 = map (fn x => parse_pair x) l1
      val l3 = map (fn (a, b) => (cand_list a, parse_number b)) l2
  in l3
  end

val first_final_test = parse_first_part "[([A,B,C],1.0),([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],3.0)]" 

(* End of first part *)

(* Start of second part *)

val second_string =  " A{5.0} B{2.0} C{3.0}"

fun parse_second_part str = 
 let val strs = String.tokens (fn x => x = #" ") str 
     fun parse_t (x :: #"{" :: t) = (cand (String.str x), Real.fromString (implode t))
 in map parse_t (map explode strs)
 end 

val second_final_test = parse_second_part second_string 

(* end of second part *)

(* start of third part *)

val third_string_f =  " A{[]} B{[]} C{[]}"
val third_string_s = " A{[([A,B,C],1.0),([A,B,C],1.0),([A,B,C],1.0),([A,C,B],1.0),([A,B,C],1.0)]} B{[([B,A,C],1.0),([B,C,A],1.0)]} C{[([C,B,A],1.0),([C,A,B],1.0),([C,B,A],1.0)]}"

fun parse_third_part str = 
 let val strs = String.tokens (fn x => x = #" ") str 
     val lstrs = map explode strs 
     fun parse_t (x :: #"{" :: t) = (cand (String.str x), 
                                     parse_first_part (implode (List.take (t, List.length t - 1))))
 in map parse_t lstrs 
 end

val third_final_test = parse_third_part third_string_s
(* end of third part *)

(* start of fourth part *)

val fourth_string = "[A,B,C]";

fun parse_fourth_part str = cand_list str 

val fourth_final_test = parse_fourth_part fourth_string

(*end of fourth part *)

(* start of fifth part *)

val fifth_string = "[A,B,C]";

fun parse_fifth_part str = cand_list str 

val fifth_final_test = parse_fifth_part fifth_string
                                         
(*end of fifth part *)

(* start of six part *)

val six_string = "[A,B,C]";

fun parse_sixth_part str = cand_list str 

val sixth_final_test = parse_sixth_part six_string
                                        
(*end of fourth part *)

(* combine all the bits *)

fun parse_whole_line str = 
  let val ssemi = String.tokens (fn x => x = #";") str 
      val (f, r1) = (List.hd ssemi, List.tl ssemi)
      val fst = List.hd (List.tl (String.tokens (fn x => x = #" ") f))
      val (s, r2) = (List.hd r1, List.tl r1) 
      val (t, r3) = (List.hd r2, List.tl r2)
      val (fr, r4) = (List.hd r3, List.tl r3)
      val (fi, r5) = (List.hd r4, List.tl r4)
      val (si, r6) = (List.hd r5, List.tl r5)
  in (parse_first_part fst, 
      parse_second_part s, 
      parse_third_part t, 
      parse_fourth_part fr, 
      parse_fifth_part fi, 
      parse_sixth_part si) end
  
val t = "state [([A,B,C],1.0),([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],1.0)]; A{0.0} B{0.0} C{0.0}; A{[]} B{[]} C{[]}; []; []; [A,B,C]" 

val all_combined_parse_tree = parse_whole_line t;

open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open stringLib  
open pairTheory  
open numLib
open numTheory
open ratTheory
open bossLib
open fracTheory 
open listLib
;
  
     
val _ = new_theory "test" ; 

val _ = Hol_datatype ` Cand = cand of string ` ; 
  
val _ = Hol_datatype `judgement =  
                                 state   of 
                                    ((Cand list) # rat) list
                                  # (Cand # rat) list
                                  # (Cand # (((Cand list) # rat) list)) list
                                  # Cand list 
                                  # Cand list
                                  # Cand list 
                               | winners of (Cand list) `;  
                                                     
val sum_aux_def = Define ` ((sum_aux []) = 0) /\
                          ( (sum_aux (h::t)) = ((SND h) + (sum_aux t)) )  `;


(*the boolian function for deciding on ewin correct application*)                       val Ewin_def = Define `
                  ((Ewin ((winners l), (j : judgement))) = F) 
               /\ ((Ewin ((j: judgement), state (ba, t, p, bl, e, h))) = F)    
               /\ (Ewin (state (ba, t, p, bl, e, h), winners l) =  
                  ( if ( (e =l) /\ (LENGTH e <= 10)) then T else F))`;
 
(*to be turned into a HOL function*)       
 val Hwin = fn
                (initial l, j) => false
              | (winners l, j) => false 
              | (j, initial l) => false       
              | (j, state s) => false
              | (state (ba, t, p, bl, e, h, q), winners l) => 
                  if (List.length (e @ h) <= 10) 
                      then
                        if (e @ h = l) 
                          then true 
                        else false
                  else false; 
  
val non_empty = Define `   (non_empty [] = F)
                        /\ (non_empty (h::t) = T) `;
   
val not_elem = Define `   (not_elem a [] = T)
                       /\ (not_elem a (h::t) = (if (a = h) then F
                                               else (not_elem a t))) `;
   
val no_dup = Define  `   (no_dup [] = T)
                      /\ (no_dup (h::t) = (if (not_elem h t) then (no_dup t)
                                           else F)) `;  
 
val rec Filter = fn  [] => []
                    |(h::t) => if (no_dup (fst h)) then
                                  if (non_empty (fst h)) 
                                    then (h :: Filter t)
                                  else Filter t
                               else Filter t ; 
 
(*the following is extra now *)
val Start = fn
                (state s, j) => false
              | (winners l, j) => false 
              | (j, initial l) => false       
              | (j, winners l) => false
              | (initial l, state (ba, t, p , bl, e, h, q)) => 
                  if ((ba = Filter l); 
                     (non_empty t); 
                     (non_empty bl); 
                     (non_empty e)) 
                                  then true
                  else false ;
 
                            
                       
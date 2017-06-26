open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open stringLib 
open pairTheory;
     
val _ = new_theory "test" ;
   
val square_def = Define `
 !n. (square n = n * n) `; 
             
val theorem_thm = `!n. n <= (square n)` ;

datatype Cand = cand of string ;    

datatype Ballot = ballot of (Cand list) * real ; 
     
datatype judgement =   initial of ((Cand list) * int) list 
                     | state   of 
                                  ((Cand list) * int)
                                * (Cand * int) list
                                * (Cand * (((Cand list) * int) list)) list
                                * Cand list 
                                * Cand list
                                * Cand list
                                * int 
                     | winners of (Cand list) ;  
          
val Ewin = fn 
              (initial l, (j:judgement) ) => false
              |(winners l, (j: judgement) ) => false 
              |( (j: judgement), initial l) => false       
              |( (j: judgement), state s) => false
              |( state (ba, t, p, bl, e, h, q), winners l) => 
                 if (List.length (e @ h) <= 10) 
                      then
                        if ((e @ h) = l) 
                          then true 
                          else false
                       else false;     

   
  
winners [cand "me"];  

datatype Nat = zero | Succ of Nat | Pred of Nat ; 

datatype Nat_judge = init of int | stat of ((Nat list) * Nat) ;            
       
stat ([Succ (zero), zero], Succ zero) = (stat ([Succ (zero)], zero)) ;

val ewin_def = Define `
 (j_1 = state (ba, t, p, bl, h, e, q)) ==> (List.length (e) = s) ==> (j_2 = winners e)`;   
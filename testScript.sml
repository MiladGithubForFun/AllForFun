open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open stringLib 
open pairTheory;
     
val _ = new_theory "test" ;

datatype Cand = cand of string ;    

datatype Ballot = ballot of (Cand list) * real ; 
    
datatype judgement =   initial of ((Cand list) * real) list 
                     | state   of 
                                  ((Cand list) * real)
                                * (Cand * real) list
                                * (Cand * (((Cand list) * real) list)) list 
                                * Cand list 
                                * Cand list
                                * Cand list
                                * real 
                     | winners of (Cand list) ;  

 
 
winners [cand "me"];  

datatype Nat = zero | Succ of Nat | Pred of Nat ; 

datatype Nat_judge = init of int | stat of ((Nat list) * Nat) ;            
       
stat ([Succ (zero), zero], Succ zero) = (stat ([Succ (zero)], zero)) ;

val ewin_def = Define `
 (j_1 = state (ba, t, p, bl, h, e, q)) ==> (List.length (e) = s) ==> (j_2 = winners e)`;   
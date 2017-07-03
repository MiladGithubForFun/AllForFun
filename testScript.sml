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
                  
        
(*the boolian function for deciding on ewin correct application*)    
val Ewin_def = Define `
        (Ewin (qu : rat) st ((winners l), (j : judgement)) = F) 
        /\ (Ewin qu st (state p, state p') = F)                
        /\ (Ewin qu st (state (ba, t, p, bl, e, h), winners l) =  
                       ( if ( (e =l) /\ (LENGTH e = st)) then T else F))`;
          
val ewin_def = Define ` ewin (qu: rat) st j1 j2 = ? u t p bl e h w.
               (j1 = state (u, t, p, bl, e, h))                 
               /\ (j2 = winners w) 
               /\ (e = w)
               /\ ((LENGTH e) = st)`;
             
val ewin_to_Ewin_thm = Q.store_thm ("ewin_to_Ewin",
 `!qu st j1 j2. (ewin qu st j1 j2) ==> (Ewin qu st (j1, j2) = T) `, 
   STRIP_TAC 
     >> STRIP_TAC 
       >> Cases_on `j1`
         >> STRIP_TAC 
           >> Cases_on `j2` 
             >> rw[ewin_def] 
               >> rw[ewin_def, Ewin_def, ewin_def]) ;     


val Ewin_to_ewin = Q.store_thm ("Ewin_to_ewin", 
 `!qu st j1 j2. (Ewin qu st (j1, j2) = T) ==> (ewin qu st j1 j2) `, 
    STRIP_TAC 
    >> STRIP_TAC 
      >> Cases_on `j1` 
        >> Cases_on `j2` 
    >- rw[Ewin_def] 
    >- (Cases_on `p` 
      >> Cases_on `r` 
        >> Cases_on `r'` 
          >> Cases_on `r` 
            >> Cases_on `r'` 
              >> rw[Ewin_def] 
                >> rw[ewin_def]) 
    >- rw[Ewin_def] 
    >-  rw[Ewin_def])  ;       
       
val Hwin_def = Define `
        (Hwin (qu : rat) st (winners l, (j : judgement)) = F) 
        /\ (Hwin qu st (state p, state p') = F)                
        /\ (Hwin qu st (state (ba, t, p, bl, e, h), winners l) =  
            ( if ( ((e ++ h) = l) /\ ((LENGTH (e ++ h)) <= st)) then T else F))`; 
  
val hwin_def = Define ` hwin (qu: rat) st j1 j2 = ? u t p bl e h w.
               (j1 = state (u, t, p, bl, e, h))                 
               /\ (j2 = winners w) 
               /\ ((e ++ h) = w)
               /\ ((LENGTH (e ++ h)) <= st)`;
   
val hwin_to_Hwin = Q.store_thm ("hwin_to_Hwin",
  `!qu st j1 j2. (hwin qu st j1 j2) ==> (Hwin qu st (j1, j2) = T)`,
   STRIP_TAC >> STRIP_TAC >> Cases_on `j1` 
   >- (rw[hwin_def]
    >> rw[Hwin_def])
   >- rw[hwin_def]); 
     
val Hwin_to_hwin = Q.store_thm ("Hwin_to_hwin", 
  `!qu st j1 j2. (Hwin qu st (j1, j2) = T) ==> (hwin qu st j1 j2)`,
   STRIP_TAC >> STRIP_TAC >> Cases_on `j1` >> Cases_on `j2`  
   >- rw[Hwin_def]
   >- (Cases_on `p` 
     >> Cases_on `r` 
       >> Cases_on `r'` 
         >> Cases_on `r` 
           >> Cases_on `r'`
             >> rw[Hwin_def] 
               >> rw[hwin_def]) 
   >- rw[Hwin_def] 
   >- rw[Hwin_def]); 
 
 
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
 
                            
                       

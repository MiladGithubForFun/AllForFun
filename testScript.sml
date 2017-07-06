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
                       ( (e =l) /\ (LENGTH e = st)))`;
          
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
            ((e ++ h) = l) /\ ((LENGTH (e ++ h)) <= st))`; 
   
val hwin_def = Define ` hwin (qu: rat) st j1 j2 = ? u t p bl e h w.
               (j1 = state (u, t, p, bl, e, h))                 
               /\ (j2 = winners w) 
               /\ ((e ++ h) = w)
               /\ ((LENGTH (e ++ h)) <= st)`;
    
val hwin_to_Hwin = Q.store_thm ("hwin_to_Hwin",
  `!qu st j1 j2. (hwin qu st j1 j2) ==> (Hwin qu st (j1, j2) = T)`,
   STRIP_TAC 
        >> STRIP_TAC 
          >> Cases_on `j1` 
   >- (rw[hwin_def]
     >> rw[Hwin_def])
   >- rw[hwin_def]); 
      
val Hwin_to_hwin = Q.store_thm ("Hwin_to_hwin", 
  `!qu st j1 j2. (Hwin qu st (j1, j2) = T) ==> (hwin qu st j1 j2)`,
   STRIP_TAC
        >> STRIP_TAC
	  >> Cases_on `j1`
	    >> Cases_on `j2`  
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
  
val eqe_def = Define `
       ((eqe (c: Cand) l nl ) = ?l1 l2. 
                                 (l = l1 ++ l2)
                                 /\ (nl = l1 ++ [c] ++ l2)
                                 /\ (~ (MEM c l1)) 
                                 /\ (~ (MEM c l2))) `;
   
val get_cand_tally_def = Define `
            (get_cand_tally (c : Cand) [] = (~ 1))
            /\ (get_cand_tally c (h ::t) = (if  (c = FST h) then SND h
                                            else (get_cand_tally c t))) `;
   
val get_cand_pile_def = Define `
     (get_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
     /\ (get_cand_pile c (h ::t) = (if (c = FST h) then SND h
                                     else get_cand_pile c t)) `;
 
val empty_cand_pile_def = Define `
   (empty_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
   /\ (empty_cand_pile c (h ::t) = (if (c = FST h) then ((c, []) :: t)
                                    else h :: (empty_cand_pile c t))) `;

         
val elim_def = Define ` (elim st (qu :rat) j1 j2) = (?t p e h nh nba np.
    (j1 = state ([], t, p, [], e, h))
    /\ (LENGTH (e ++ h) > st) 
    /\ (LENGTH e < st)
    /\ (!c. (MEM c h ==> (!x. MEM (c,x) t ==> ( x < qu))))  
    /\ (?c'. (MEM c' h) 
          /\ (!d. (MEM d h ==> (!x y. (MEM (c',x) t) /\ (MEM (d,y) t) ==> ( x <= y))))
      /\ (?l1 l2. (nh = l1 ++l2) /\ (h = l1 ++ [c']++ l2) /\ ~ (MEM c' l1) /\ ~(MEM c' l2))
      /\ (nba = get_cand_pile c' p)
      /\ ( MEM (c',[]) np)
      /\ (!d'. ((d' <> c') ==> (!l. (MEM (d',l) p ==> MEM (d',l) np) 
                                 /\ (MEM (d',l) np ==> MEM (d',l) p))))
      /\ (j2 = state (nba, t, np, [], e, nh)))) `; 
               

val less_than_quota_def = Define `
                 (less_than_quota qu [] l = T)
              /\ (less_than_quota qu (h ::tl ) l = (if (get_cand_tally h l < qu) 
                                                         then less_than_quota qu tl l
                                                    else F)) `; 

(*to find the weakest candidate in a non-empty list of continuing candidates*)   
val find_weakest_cand_def = Define `
           (find_weakest_cand [h] l = h)
        /\ (find_weakest_cand (h::h'::tl) l = (if (get_cand_tally h l <= get_cand_tally h' l)
                                                      then find_weakest_cand (h::tl) l                                                         else find_weakest_cand (h'::tl) l)) `;
 
 
(*checks if c is the weakest w.r.t. all the other continuing candidates*)
val is_weakest_cand_def = Define `
             (is_weakest_cand (c: Cand) [] l = T)
          /\ (is_weakest_cand (c: Cand) (h::t) l = (if (get_cand_tally c l < get_cand_tally c l)
                                                        then is_weakest_cand c t l
                                                    else F)) `;

val remove_one_cand_def = Define `
                         (remove_one_cand (c :Cand) [] = [])
                      /\ (remove_one_cand c (h::t) = (if c = h then t 
                                                      else h:: remove_one_cand c t)) `;
   
val non_empty = Define ` (non_empty [] = F)
                      /\ (non_empty _ = T) `;
 

val empty_list_def = Define `
                         (empty_list [] = T)
                      /\ (empty_list _ = F) `;
   
val APPEND_NIL_LEFT = Q.store_thm ("APPEND_NIL_LEFT", 
                                                `!l. [] ++ l = l `,
                                                       STRIP_TAC >> EVAL_TAC) ;  

val APPEND_NIL_LEFT_COR = Q.store_thm("APPEND_NIL_lEFT_COR", 
                                             `!h t. [] ++ (h::t) = h::t `,
                                                   rw[APPEND_NIL_LEFT]) ;
   
val APPEND_EQ_NIL = Q.store_thm ("APPEND_EQ_NIL",
    `!l1 l2. ([] = l1 ++ l2) ==> ((l1 = []) /\ (l2 = [])) `,
      Cases_on `l2`
        >- ASM_SIMP_TAC bool_ss [APPEND_NIL]    
        >- (Cases_on `l1` 
          >> rw[APPEND_NIL_LEFT_COR]   
            >> (ASM_SIMP_TAC bool_ss [NOT_NIL_CONS] 
              >> STRIP_TAC 
                >> rw[NOT_NIL_CONS]))) ;
  
val APPEND_MID_NOT_NIL = Q.store_thm ("APPEND_MID_NOT_NIL",
       `!l1 l2 c. ([] = l1 ++([c]++l2)) = F `,
           Induct_on `l1` 
            >> rw[APPEND]) ;  
    

`!c h h'. (?l1 l2. (h = l1++l2) 
                /\ (h' = l1++([c]++l2)) 
                /\ ~(MEM c l1) 
                /\ ~(MEM c l2)) ==> (h = remove_one_cand c h')`

STRIP_TAC Induct_on `h'`  
>- rw[APPEND_MID_NOT_NIL]

STRIP_TAC STRIP_TAC   
     

 
  
  
         


Induct_on `h` 
ASM_SIMP_TAC bool_ss []


    
          
val Elim_def = Define `
             (Elim st (qu : rat) ((j: judgement), winners w) = F)
          /\ (Elim st qu (winners w, (j: judgement)) = F) 
          /\ (Elim st qu (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) = (?c.
                  ((empty_list ba) 
               /\ (empty_list bl) 
               /\ (t = t') /\ (bl = bl') /\ (e = e')
               /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
               /\ (MEM c h)
               /\ (less_than_quota qu h t)
               /\ (c = find_weakest_cand h t)
               /\ (h' = remove_one_cand c h)
               /\ (is_weakest_cand c h t)
               /\ (eqe c h' h)
               /\ (ba' = get_cand_pile c p)
               /\ (p' = empty_cand_pile c p) ))) `;
                 
`!st qu j1 j2. (Elim st qu (j1,j2) = T) ==> (elim st qu j1 j2) `
STRIP_TAC STRIP_TAC 
Cases_on `j1` Cases_on `j2`  Cases_on `p` Cases_on `r` Cases_on `r'` Cases_on `r` 
Cases_on `r'` Cases_on `p'` Cases_on `r'` Cases_on `r''` Cases_on `r'` Cases_on `r''` 
rw[Elim_def] rw[elim_def] 
 



`!st qu j1 j2. ((elim st qu j1 j2) ==> (Elim st qu (j1, j2) = T))`                   


   
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
                            
                       

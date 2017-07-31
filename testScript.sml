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
           (get_cand_tally (c: Cand) (h ::t) = (if  (c = FST h) then SND h
                                            else (get_cand_tally c t))) `;
      
val get_cand_pile_def = Define `
     (get_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
     /\ (get_cand_pile c (h ::t) = (if (c = FST h) then SND h
                                     else get_cand_pile c t)) `;
 
val empty_cand_pile_def = Define `
   (empty_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
   /\ (empty_cand_pile c (h ::t) = (if (c = FST h) then ((c, []) :: t)
                                    else h :: (empty_cand_pile c t))) `;

(*a legal tally consists of all of the initial Candidates each of whom appers only once in the list*)     
val legal_tally_cand_def = Define ` 
   (legal_tally_cand l t (c: Cand) =  (MEM c l) 
                /\ (?l1. (?(x:rat) l2. (t = l1 ++ [(c,x)] ++ l2) 
                                   /\ (~ MEM c (MAP FST l1))
                                   /\ (~ MEM c (MAP FST l2))))) `;
      
    
 
val Legal_Tally_Cand_def = Define `
      (Legal_Tally_Cand l ([]: (Cand # rat) list) (c:Cand) = F)
   /\ (Legal_Tally_Cand l (h::t) c =  (MEM c l) 
                                   /\ (if (FST h = c) then (~ MEM c (MAP FST t)) 
                                       else Legal_Tally_Cand l t c)) `;
   
val CAND_EQ_DEC = Q.store_thm ("CAND_EQ_DEC", 
    `!(c1: Cand) c2. (c1 = c2) \/ (c1 <> c2) `,
       REPEAT STRIP_TAC 
          >> Cases_on `c1 = c2` 
             >- (DISJ1_TAC >> METIS_TAC []) 
             >- (DISJ2_TAC >> METIS_TAC []));    
           
val GET_CAND_TALLY_HEAD_REMOVAL_def = Q.store_thm ("GET_CAND_TALLY_HEAD_REM",
`!(h: Cand #rat) t c. (~(c = FST h)) ==> (get_cand_tally c (h::t) = get_cand_tally c t)`,  Induct_on `t` 
               >- rw [get_cand_tally_def] 
               >- (REPEAT STRIP_TAC 
                 >> first_assum (qspecl_then [`h'`,`c`] strip_assume_tac) 
                   >> EVAL_TAC 
                     >> rw []));  
  
 
val GET_CAND_TALLY_MEM_def = Q.store_thm ("GET_CAND_TALLY_MEM",
 `!(h: Cand # rat) t c. (MEM c (MAP FST (h::t))) 
                                    ==> (MEM (c, get_cand_tally c (h::t)) (h::t)) `, 
   Induct_on `t`      
       >- (EVAL_TAC 
         >> STRIP_TAC 
          >> STRIP_TAC 
           >> STRIP_TAC 
            >> rw[])       
       >- ((ASSUME_TAC CAND_EQ_DEC 
        >> REPEAT STRIP_TAC 
         >> first_assum (qspecl_then [`c`,`FST h'`] strip_assume_tac))   
           >- (rw[] 
            >> EVAL_TAC 
              >> DISJ1_TAC >> ASM_SIMP_TAC bool_ss [PAIR])        
           >- ((ASSUME_TAC MEM 
            >> ASSUME_TAC (INST_TYPE [alpha|-> ``:(Cand # rat)``,beta|-> ``:Cand``] MAP)
              >> first_assum (strip_assume_tac) 
               >> first_x_assum (qspecl_then [`FST`,`h'`,`h::t`] strip_assume_tac) 
                >> first_x_assum (qspecl_then [`h`,`c`] strip_assume_tac) 
                 >> RW_TAC bool_ss [] 
                  >> FULL_SIMP_TAC list_ss [])
                    >- (DISJ2_TAC 
                      >> DISJ1_TAC 
                        >> EVAL_TAC 
                         >> rw[])     
                    >- (DISJ2_TAC 
                      >> RW_TAC bool_ss [GET_CAND_TALLY_HEAD_REMOVAL_def]))));
    
        
 
val Legal_to_legal_tally_cand = Q.store_thm("Legal_to_legal_tally_cand",
   `!l  (t: (Cand # rat) list) c. (Legal_Tally_Cand l t c) ==> (legal_tally_cand l t c) `,                           
 
     Induct_on `t`          
       >- ASM_SIMP_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def]             
       >- ((ASSUME_TAC CAND_EQ_DEC 
         >> STRIP_TAC 
          >> STRIP_TAC 
           >> STRIP_TAC 
            >> first_assum (qspecl_then [`c`,`FST h`] strip_assume_tac))    
              >- (RW_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def] 
                >> MAP_EVERY qexists_tac [`[]`, `SND h`,`t`] 
                  >> rw[])   
              >- (first_assum (qspecl_then [`l`,`c`] strip_assume_tac) 
                >> FULL_SIMP_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def] 
                 >> STRIP_TAC 
                   >> FULL_SIMP_TAC bool_ss [] 
                     >> MAP_EVERY qexists_tac [`h::l1`,`x`,`l2`] 
                      >> rw[]))) ;  
      
val legal_to_Legal_tally_cand = Q.store_thm ("legal_to_Legal_tallt_cand",
    `!l (t: (Cand # rat) list) c. (legal_tally_cand l t c) ==> (Legal_Tally_Cand l t c) `,
 
      Induct_on `t`      
        >- rw[legal_tally_cand_def, Legal_Tally_Cand_def] 
   
          >- ((STRIP_TAC 
           >> STRIP_TAC 
            >> STRIP_TAC 
             >> ASSUME_TAC CAND_EQ_DEC 
              >> first_assum (qspecl_then [`c`,`FST h`] strip_assume_tac))      
          >- ((RW_TAC bool_ss [legal_tally_cand_def, Legal_Tally_Cand_def] 
            >> ASSUME_TAC (INST_TYPE [alpha |-> ``:(Cand #rat)``] list_nchotomy) 
              >> first_assum (qspecl_then [`l1`] strip_assume_tac))
                >- FULL_SIMP_TAC bool_ss [APPEND,APPEND_NIL,CONS_11] 
                >- (FULL_SIMP_TAC bool_ss [APPEND,CONS_11] 
                  >> rw [] 
                    >> FULL_SIMP_TAC bool_ss [MEM,MAP]))
        >- ((STRIP_TAC 
          >> RW_TAC bool_ss [legal_tally_cand_def,Legal_Tally_Cand_def])  
             >- FULL_SIMP_TAC bool_ss [legal_tally_cand_def]  
             >- ((first_assum (qspecl_then [`l`,`c`] strip_assume_tac) 
               >> FULL_SIMP_TAC bool_ss [legal_tally_cand_def] 
                 >> ASSUME_TAC (INST_TYPE [alpha |-> ``:(Cand #rat)``] list_nchotomy)
                   >> first_assum (qspecl_then [`l1`] strip_assume_tac)) 
                     >- FULL_SIMP_TAC bool_ss [APPEND,APPEND_NIL,CONS_11,FST]           
                     >- (rw [] 
                       >> FULL_SIMP_TAC bool_ss [APPEND,CONS_11,MAP,MEM] 
                         >> rw [] 
                           >> METIS_TAC []))))) ;
    
val remove_one_cand_def = Define `
                         (remove_one_cand (c :Cand) [] = [])
                      /\ (remove_one_cand c (h::t) = (if c = h then t 
                                                      else h:: remove_one_cand c t)) `;

 val not_elem = Define `   (not_elem a [] = T)
                       /\ (not_elem a (h::t) = (if (a = h) then F
                                               else (not_elem a t))) `;
   
val no_dup = Define  `   (no_dup [] = T)
                      /\ (no_dup (h::t) = (if (not_elem h t) then (no_dup t)
                                           else F)) `;  

(* the following predicate states when a list is duplicate-free w.r.t. a particular candidate*) 
val NO_DUP_PRED = Define `
   (NO_DUP_PRED h (c: Cand) = (h = []) \/ (~ MEM c h) \/ 
                              (?h1 h2. (h = h1 ++ [c]++ h2) /\ (~ MEM c h1) /\ (~ MEM c h2))) `;  
  

val not_elem_NOT_MEM = Q.store_thm ("not_elem_NOT_MEM",
   `!h (c: Cand). (not_elem c h) <=> (~MEM c h)`,
 
      Induct_on `h`
           >- rw [not_elem] 
           >- rw[not_elem]);  
 
         
val no_dup_IMP_NO_DUP_PRED = Q.store_thm ("no_dup_IMP_NO_DUP",
   ` !h (c :Cand). (no_dup h ) ==> (NO_DUP_PRED h c) `,

     Induct_on `h`
         >- rw [NO_DUP_PRED]  
         >- ((STRIP_TAC >> STRIP_TAC >> ASSUME_TAC CAND_EQ_DEC 
           >> first_x_assum (qspecl_then [`c`,`h'`] strip_assume_tac))                
              >- (first_assum (qspecl_then [`c`] strip_assume_tac) 
                >> RW_TAC bool_ss [NO_DUP_PRED,no_dup]  
                  >> DISJ2_TAC 
                    >> MAP_EVERY qexists_tac [`[]`,`h`] 
                      >> rw [] 
                        >> ASSUME_TAC not_elem_NOT_MEM  
                          >> first_assum (qspecl_then [`h`,`c`] strip_assume_tac) 
                            >> FULL_SIMP_TAC bool_ss [])  
              >- ((first_x_assum (qspecl_then [`c`] strip_assume_tac) 
                >> STRIP_TAC  
                  >> FULL_SIMP_TAC bool_ss [NO_DUP_PRED,no_dup])   
                     >- (DISJ2_TAC >> rw [])  
                     >- (DISJ2_TAC >> rw []) 
                     >- (REPEAT DISJ2_TAC 
                       >> MAP_EVERY qexists_tac [`h'::h1`,`h2`] 
                         >> METIS_TAC [APPEND,MEM])))); 
          
val NO_DUP_HEAD_REMOVAL = Q.store_thm ("NO_DUP_HEAD_REMOVAL",
    `!h h'. (!(c: Cand). NO_DUP_PRED (h'::h) c) ==> (!c. NO_DUP_PRED h c) `,
  
        (rw [NO_DUP_PRED] >> first_assum (qspecl_then [`c`] strip_assume_tac))
          >- (DISJ2_TAC >> DISJ1_TAC >> rw []) 
          >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy)
            >> first_assum (qspecl_then [`h1`] strip_assume_tac))
              >- (DISJ2_TAC 
                >> DISJ1_TAC 
                  >> FULL_SIMP_TAC bool_ss [APPEND,CONS_11])  
              >- (REPEAT DISJ2_TAC 
                 >> MAP_EVERY qexists_tac [`t`,`h2`] 
                   >> FULL_SIMP_TAC list_ss [CONS_11,MEM])));         
           
 

val NO_DUP_PRED_to_no_dup = Q.store_thm ("NO_DUP_PRED_to_no_dup",
  `!h. (!(c: Cand). (NO_DUP_PRED h c)) ==> (no_dup h) `,
 
     Induct_on `h`
         >- rw [no_dup]  
         >- ((STRIP_TAC 
           >> STRIP_TAC 
             >> ASSUME_TAC NO_DUP_HEAD_REMOVAL 
               >> first_assum (qspecl_then [`h`,`h'`] strip_assume_tac) 
                 >> FULL_SIMP_TAC bool_ss [] 
                   >> rw[no_dup] 
                     >> first_assum (qspecl_then [`h'`] strip_assume_tac) 
                       >> FULL_SIMP_TAC list_ss [NO_DUP_PRED,not_elem_NOT_MEM,MEM] 
                         >> ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy) 
                           >> first_assum (qspecl_then [`h1`] strip_assume_tac))
                              >- FULL_SIMP_TAC list_ss [CONS_11,MEM]          
                              >- FULL_SIMP_TAC list_ss [CONS_11,MEM]));
   
  








   ASSUME_TAC CAND_EQ_DEC   
   first_x_assum (qspecl_then [`c`,`h'`] strip_assume_tac)
   
      first_assum (qspecl_then [`c`] strip_assume_tac)
      FULL_SIMP_TAC bool_ss [NO_DUP_PRED,MEM]               
         
          rw[no_dup]                             
         
          METIS_TAC []

          




Induct_on `h` 
  rw [no_dup] 
     
  STRIP_TAC STRIP_TAC ASSUME_TAC CAND_EQ_DEC   
  first_x_assum (qspecl_then [`c`,`h'`] strip_assume_tac) 
          rw [NO_DUP_PRED,no_dup]     
                
               ASSUME_TAC (INST_TYPE  [alpha |-> ``:Cand``] list_nchotomy)  
               first_assum (qspecl_then [`h1`] strip_assume_tac)
                     
                    METIS_TAC [CONS_11,APPEND_NIL,APPEND,not_elem_NOT_MEM]
            
                    METIS_TAC [CONS_11,APPEND,APPEND_NIL,not_elem_NOT_MEM,MEM] 
       
               first_assum (qspecl_then [`c`] strip_assume_tac)            
               ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy) 
               first_x_assum (qspecl_then [`h1`] strip_assume_tac) 
                       
                       FULL_SIMP_TAC bool_ss [CONS_11,NO_DUP_PRED,MEM,APPEND,APPEND_NIL]                
                       
                       METIS_TAC [CONS_11,APPEND,APPEND_NIL,not_elem_NOT_MEM,MEM]  
          
          rw [NO_DUP_PRED,no_dup,MEM] 
 





`!h1 h2 (c: Cand). (h2 = remove_one_cand c h1) <=> (eqe c h2 h1) `

val elim_cand_def = Define ` (elim_cand st (qu :rat) (l : Cand list) (c: Cand) j1 j2) = (?t p e h nh nba np.
    (j1 = state ([], t, p, [], e, h))
    /\ (LENGTH (e ++ h) > st) 
    /\ (LENGTH e < st)
    /\ (!c'. legal_tally_cand l t c')
    /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))  
    /\ (MEM c h) 
    /\ (!d. (MEM d h ==> (?x y. (MEM (c,x) t) /\ (MEM (d,y) t) /\ ( x <= y))))
    /\ (?l1 l2. (nh = l1 ++l2) /\ (h = l1 ++ [c]++ l2) /\ ~ (MEM c l1) /\ ~(MEM c l2)
    /\ (nba = get_cand_pile c p)
    /\ ( MEM (c,[]) np)
    /\ (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p ==> MEM (d',l) np) 
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
 
STRIP_TAC SPEC_TAC(h'', (!h   
     

 
  
  
         


Induct_on `h` 
ASM_SIMP_TAC bool_ss []


    
           
val Elim_def = Define `
             (Elim st (qu : rat) ((j: judgement), winners w) = F)
          /\ (Elim st qu (winners w, (j: judgement)) = F) 
          /\ (Elim st qu (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) = 
                  ((empty_list ba) 
               /\ (empty_list bl) 
               /\ (t = t') /\ (bl = bl') /\ (e = e')
               /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
               /\ (MEM (find_weakest_cand h t) h)
               /\ (less_than_quota qu h t)
               /\ (h' = remove_one_cand (find_weakest_cand h t) h)
               /\ (is_weakest_cand (find_weakest_cand h t) h t)
               /\ (ba' = get_cand_pile (find_weakest_cand h t) p)
               /\ (p' = empty_cand_pile (find_weakest_cand h t) p) )) `;
                  
`!st qu j1 j2. (Elim st qu (j1,j2) = T) ==> (elim st qu j1 j2) `
STRIP_TAC STRIP_TAC 
Cases_on `j1` Cases_on `j2`  Cases_on `p` Cases_on `r` Cases_on `r'` Cases_on `r` 
Cases_on `r'` Cases_on `p'` Cases_on `r'` Cases_on `r''` Cases_on `r'` Cases_on `r''` 
rw[Elim_def] rw[elim_def] 
 



`!st qu j1 j2. ((elim st qu j1 j2) ==> (Elim st qu (j1, j2) = T))`                   


   

 
val rec Filter = fn  [] => []
                    |(h::t) => if (no_dup (fst h)) then
                                  if (non_empty (fst h)) 
                                    then (h :: Filter t)
                                  else Filter t
                               else Filter t ; 
                            
                       

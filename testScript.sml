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
  
 

val GET_CAND_TALLY_MEM2 = Q.store_thm ("GET_CAND_TALLY_MEM",
 `!(t: (Cand #rat) list) c. (MEM c (MAP FST t)) 
                                    ==> (MEM (c, get_cand_tally c t) t) `, 
   
    Induct_on `t`
        >- rw []
        >- (EVAL_TAC 
          >> REPEAT STRIP_TAC >> rw []));

 
*------------------------------------------*
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
    
*---------------------------------------------------*
         
 
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
   

val NO_DUP_TAIL_ONE_CAND = Q.store_thm ("NO_DUP_TAIL_ONE_CAND",
  `!h h' (c:Cand). (NO_DUP_PRED (h'::h) c) ==> (NO_DUP_PRED h c)`,    

     (REPEAT STRIP_TAC 
       >> ASSUME_TAC CAND_EQ_DEC 
         >> first_assum (qspecl_then [`c`,`h'`] strip_assume_tac)) 
            >-  (FULL_SIMP_TAC bool_ss [NO_DUP_PRED] 
                >- rw[] 
                >-  METIS_TAC [MEM]  
                >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy) 
                  >> first_assum (qspecl_then [`h1`] strip_assume_tac))
                     >- FULL_SIMP_TAC list_ss [MEM,CONS_11]
                     >- FULL_SIMP_TAC list_ss [MEM,CONS_11]))
            >-  (FULL_SIMP_TAC bool_ss [NO_DUP_PRED]  
                >- rw []
                >- (DISJ2_TAC >> METIS_TAC [MEM]) 
                >- ((REPEAT DISJ2_TAC 
                  >> ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy)  
                    >> first_assum (qspecl_then [`h1`] strip_assume_tac)) 
                       >- FULL_SIMP_TAC list_ss [MEM,CONS_11] 
                       >- (FULL_SIMP_TAC list_ss [MEM,CONS_11] 
                         >> MAP_EVERY qexists_tac [`t`,`h2`] 
                           >> METIS_TAC [])))) ;  
     
val Valid_Init_CandList = Define `
     Valid_Init_CandList (l: Cand list) = ((l <> []) /\ (!c. NO_DUP_PRED l c)) `; 
                                                 
 
val Valid_CandTally = Define `
     Valid_CandTally (t: (Cand # rat) list) l = (!c. (MEM c l) <=> (MEM c (MAP FST t))) `;

   
val Valid_CandTally_DEC1_def = Define `
        (Valid_CandTally_DEC1 ([]: (Cand #rat) list) l = T)
     /\ (Valid_CandTally_DEC1 (h::t) l = (MEM (FST h) l) /\ (Valid_CandTally_DEC1 t l)) `;
          
val Valid_CandTally_DEC2_def = Define `
        (Valid_CandTally_DEC2 (t: (Cand # rat) list) [] = T) 
     /\ (Valid_CandTally_DEC2 t (l0::ls) = if (MEM l0 (MAP FST t)) 
                                                then (Valid_CandTally_DEC2 t ls)
                                           else F) `;
 
val non_empty = Define ` (non_empty [] = F)
                      /\ (non_empty _ = T) `;
 

val empty_list_def = Define `
                         (empty_list [] = T)
                      /\ (empty_list _ = F) `;
 



val CandTally_to_CandTally_DEC1 = Q.store_thm ("CandTally_to_CandTally_DEC1",
 `!l t. (!c. (MEM c (MAP FST t)) ==> (MEM c l)) ==> (Valid_CandTally_DEC1 t l) `,

    Induct_on `t` 
       >- rw [Valid_CandTally_DEC1_def]
       >- (REPEAT STRIP_TAC 
          >> first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[Valid_CandTally_DEC1_def,MAP]));
                                                                                                                                                                                             
val CandTally_DEC1_to_CandTally = Q.store_thm ("CandTally_DEC1_to_CandTally",
 `!l t. (Valid_CandTally_DEC1 t l) ==> (!c. MEM c (MAP FST t) ==> (MEM c l))`,
 
    Induct_on `t`  
        >- rw[]
        >- (REPEAT STRIP_TAC     
            >> rfs [Valid_CandTally_DEC1_def])); 

  
  
val non_empty_IS_CORRECT = Q.store_thm ("non_empty_IS_CORRECT",
  `!(l: (Cand # rat) list). (non_empty l) ==> (?l0 ls. (l = l0::ls)) `,
 
     (STRIP_TAC 
       >> ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand #rat``] list_nchotomy)   
         >> first_assum (qspecl_then [`l`] strip_assume_tac))   
            >- rw [non_empty]   
            >- rw[non_empty]);
 

val CandTally_DEC1_IMP_CandTally= Q.store_thm ("CandTally_DEC1_IMP_CandTally",
  `!l t. (Valid_CandTally_DEC1 t l) /\ (non_empty t) ==> (!c. MEM c (MAP FST t) ==> (MEM c l))`,

      (REPEAT STRIP_TAC 
        >> ASSUME_TAC non_empty_IS_CORRECT 
          >> first_x_assum (qspecl_then [`t`] strip_assume_tac) 
            >> `?t0 t1. (t = t0::t1)` by metis_tac [] 
              >> RW_TAC bool_ss [] 
                >> Induct_on `t1`) 
                  >- rw[Valid_CandTally_DEC1_def]  
                  >- ((REPEAT STRIP_TAC    
                    >> rfs []) 
                       >- rfs [Valid_CandTally_DEC1_def]
                       >- rfs [Valid_CandTally_DEC1_def]
                       >- rfs [Valid_CandTally_DEC1_def,non_empty])); 
    
     
    
val CandTally_to_CandTally_DEC2 = Q.store_thm ("CandTally_to_CandTally_DEC2",
   `!l t. (!c. (MEM c l) ==> (MEM c (MAP FST t))) ==> (Valid_CandTally_DEC2 t l) `,

     Induct_on `l`
        >- rw [Valid_CandTally_DEC2_def]
        >- rfs [Valid_CandTally_DEC2_def]); 
    
      
val CandTally_DEC2_IMP_CandTally = Q.store_thm ("CandTally_DEC2_IMP_CandTally",
  `!l t. (Valid_CandTally_DEC2 t l) ==> (!c. (MEM c l) ==> (MEM c (MAP FST t)))`,

     Induct_on `l`
         >- rw []
         >- ((REPEAT STRIP_TAC  
           >> FULL_SIMP_TAC list_ss [MEM])
              >- FULL_SIMP_TAC list_ss [Valid_CandTally_DEC2_def]
              >- rfs [Valid_CandTally_DEC2_def]));
 
 
val REMOVE_ONE_CAND_APPEND = Q.store_thm ("REMOVE_ONE_CAND_APPEND",
 `! l1 l2 (c: Cand). (~ MEM c l1) ==> (remove_one_cand c (l1 ++l2) = l1 ++ (remove_one_cand c l2))`,

   Induct_on `l1`  
       >- RW_TAC list_ss [APPEND_NIL,remove_one_cand_def]
       >- (REPEAT STRIP_TAC
         >> first_assum (qspecl_then [`l2`,`c`] strip_assume_tac)
           >> FULL_SIMP_TAC list_ss [MEM,remove_one_cand_def])); 
 
 
val REMOVE_ONE_CAND_NOTIN = Q.store_thm ("REMOVE_ONE_CAND_NOTIN",
 `!l (c: Cand). (~ MEM c l) ==> (remove_one_cand c l = l) `,

    Induct_on `l`
        >- rw [remove_one_cand_def]
        >- (REPEAT STRIP_TAC 
          >> FULL_SIMP_TAC list_ss [MEM, remove_one_cand_def])) ;  



val EQE_REMOVE_ONE_CAND = Q.store_thm ("EQE_REMOVE_ONE_CAND",
  `!h (c: Cand). (MEM c h) /\ (NO_DUP_PRED h c) ==> (eqe c (remove_one_cand c h) h) `,
 
 Induct_on `h`  
     >- rw []       
  
     >- ((STRIP_TAC 
       >> STRIP_TAC 
         >> ASSUME_TAC CAND_EQ_DEC
           >> first_x_assum (qspecl_then [`c`,`h'`] strip_assume_tac))    
               >- ((rw[eqe_def,remove_one_cand_def,NO_DUP_PRED] 
                  >> MAP_EVERY qexists_tac [`[]`,`h`] 
                     >> EVAL_TAC   
                       >> ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy)   
                         >> first_assum (qspecl_then [`h1`] strip_assume_tac))  
                             >- FULL_SIMP_TAC list_ss [CONS_11,MEM]  
                             >- FULL_SIMP_TAC list_ss [list_11,MEM])  
               >- ((STRIP_TAC 
                  >> first_x_assum (qspecl_then [`c`] strip_assume_tac) 
                    >> ASSUME_TAC NO_DUP_TAIL_ONE_CAND 
                       >> first_x_assum (qspecl_then [`h`,`h'`,`c`] strip_assume_tac)  
                         >> FULL_SIMP_TAC list_ss [MEM])          
                             >- rw []   
                             >-  (`eqe c (remove_one_cand c h) h ` by metis_tac []
                               >> FULL_SIMP_TAC bool_ss [eqe_def,remove_one_cand_def]          
                                 >> MAP_EVERY qexists_tac [`h'::l1`,`l2`] 
                                   >> RW_TAC list_ss [MEM])))) ;         
                              
              
val EQE_IMP_REMOVE_ONE_CAND = Q.store_thm ("EQE_IMP_REMOVE_ONE_CAND",
 `!h1 h2 (c: Cand). (MEM c h2) /\ (eqe c h1 h2) ==> (h1 = remove_one_cand c h2) `,

   REPEAT STRIP_TAC 
     >> FULL_SIMP_TAC list_ss [eqe_def]  
       >> ASSUME_TAC REMOVE_ONE_CAND_APPEND  
         >> FULL_SIMP_TAC list_ss [eqe_def,remove_one_cand_def]
           >> first_assum (qspecl_then [`l1`,`[c]++l2`,`c`] strip_assume_tac)  
             >> rfs [remove_one_cand_def]);   
 
 
val APPEND_NIL_LEFT = Q.store_thm ("APPEND_NIL_LEFT", 
                                                `!l. [] ++ l = l `,
                                                       STRIP_TAC >> EVAL_TAC) ;  

val APPEND_NIL_LEFT_COR = Q.store_thm("APPEND_NIL_lEFT_COR", 
                                             `!h t. [] ++ (h::t) = h::t `,
                                                   rw[APPEND_NIL_LEFT]) ;
 


val MAP_APPEND_TRIO = Q.store_thm ("MAP_APPEND_TRIO",
  `!t l1 l0 l2. (t = l1 ++ [l0] ++ l2) ==> (MAP FST t = (MAP FST l1) ++ [FST l0] ++ (MAP FST l2))`,

     REPEAT STRIP_TAC
          >> `l1 ++ [l0] ++ l2 = l1 ++([l0] ++ l2)` by FULL_SIMP_TAC list_ss [APPEND_ASSOC]  
            >> RW_TAC bool_ss []  
              >> rfs [MAP_APPEND]);
   
 
val NoDupCand_BOTH_SIDES= Q.store_thm ("NoDupCand_BOTH_SIDES",
 `!l1 l2 (c:Cand) (h1: Cand list) h2. (l1 ++ [c] ++ l2 = h1 ++ [c] ++ h2) 
                                      /\ (~ MEM c h1) /\ (~ MEM c h2) ==> (~ MEM c l1) `,

    Induct_on `l1`
         >- rw []
         >- ((REPEAT STRIP_TAC 
           >> ASSUME_TAC CAND_EQ_DEC 
              >> first_assum (qspecl_then [`c`,`h`] strip_assume_tac))   
                  >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy) 
                    >> first_assum (qspecl_then [`h1`] strip_assume_tac))   
                       >- (FULL_SIMP_TAC list_ss [CONS_11,MEM_APPEND] 
                        >> `l1++ [h]++ l2 = l1 ++ ([h]++l2)` by metis_tac[APPEND_ASSOC] 
                           >> RW_TAC bool_ss [] 
                              >> FULL_SIMP_TAC list_ss []) 
                       >- FULL_SIMP_TAC list_ss [list_11])
                  >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] list_nchotomy) 
                     >> first_assum (qspecl_then [`h1`] strip_assume_tac))
                        >- FULL_SIMP_TAC list_ss [CONS_11]
                        >- (FULL_SIMP_TAC list_ss [list_11] 
                          >> first_assum (qspecl_then [`l2`,`c`,`t`,`h2`] strip_assume_tac) 
                            >> METIS_TAC [])))) ;
              
 
val get_cand_tally_APPEND = Q.store_thm ("get_cand_tally_APPEND",
  `!(l1: (Cand #rat) list) l2 c. (~ MEM c (MAP FST l1)) 
                                  ==> (get_cand_tally c (l1++l2) = get_cand_tally c l2) `,

      Induct_on `l1`
           >- rw[APPEND_NIL,get_cand_tally_def]
           >- (REPEAT STRIP_TAC >> FULL_SIMP_TAC list_ss [MEM,MAP,get_cand_tally_def])) ;  
 
 
val EVERY_CAND_HAS_ONE_TALLY = Q.store_thm ("EVERY_CAND_HAS_ONE_TALLY",
  `!l t c (x: rat). (NO_DUP_PRED (MAP FST t) c) /\ (MEM (c,x) t) ==> (get_cand_tally c t = x) `,
 
      (REPEAT STRIP_TAC 
           >> FULL_SIMP_TAC list_ss [MEM_SPLIT]  
             >> `MAP FST t = (MAP FST l1) ++ ([c] ++ (MAP FST l2))` by 
                 rfs [MAP_APPEND_TRIO,APPEND_ASSOC,APPEND_11]   
                   >> FULL_SIMP_TAC list_ss [NO_DUP_PRED] 
                     >> ASSUME_TAC NoDupCand_BOTH_SIDES 
                       >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST l2`,`c`,`h1`,`h2`] 
                          strip_assume_tac) 
                          >> rfs [get_cand_tally_def,get_cand_tally_APPEND])); 
 
 
val less_than_quota_def = Define `
                 (less_than_quota qu [] l = T)
              /\ (less_than_quota qu (h ::tl ) l = (if (get_cand_tally h l < qu) 
                                                         then less_than_quota qu tl l
                                                    else F)) `; 
 
  
 
val LESS_THAN_QUOTA_OK = Q.store_thm ("LESS_THAN_QUOTA_OK",
`!qu t0 t1 h. (less_than_quota qu h (t0::t1)) ==> (!c.(MEM c h) ==> (get_cand_tally c (t0::t1) < qu))`,
      
    Induct_on `h`
       >- rw []
       >- (REPEAT STRIP_TAC 
         >> FULL_SIMP_TAC list_ss [MEM,less_than_quota_def,get_cand_tally_def]));
  

  


             
val less_than_qu_IMP_LogicalLessThanQuota = Q.store_thm ("less_than_qu_IMP_LogicalLessThanQuota",
 `!h t0 t1 (qu:rat). (less_than_quota qu h (t0::t1)) /\ (Valid_CandTally_DEC2 (t0::t1) h) ==> 
           (!c. (MEM c h) ==> ?x. (MEM (c,x) (t0::t1)) /\ (x < qu))`, 
    
       Induct_on `h`
          >- rw []    
          >- ((REPEAT STRIP_TAC    
            >> FULL_SIMP_TAC bool_ss [MEM])   
             >- ((ASSUME_TAC CandTally_DEC2_IMP_CandTally   
                >> first_x_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)   
                  >> `!c. MEM c (h'::h) ==> (MEM c (MAP FST (t0::t1))) ` by metis_tac []  
                     >> `!(h: (Cand#rat)) t c. (MEM c (MAP FST (h::t))) 
                                 ==> (MEM (c,get_cand_tally c (h::t)) (h::t))`                        
                        by (ASSUME_TAC GET_CAND_TALLY_MEM2 
                         >> REPEAT STRIP_TAC    
                         >> first_x_assum (qspecl_then [`h''::t`,`c'`] strip_assume_tac) 
                         >> rw [])                          
                          >> first_assum (qspecl_then [`h'`] strip_assume_tac)      
                            >> first_assum (qspecl_then [`t0`,`t1`,`h'`] strip_assume_tac) >> rfs[])   
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`            
                               >> rfs [less_than_quota_def])                
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`  
                              >> rw [] >> ASSUME_TAC LESS_THAN_QUOTA_OK 
                               >> first_x_assum (qspecl_then [`qu`,`t0`,`t1`,`c::h`] strip_assume_tac) 
                                >> rfs [])) 
             >- (first_assum (qspecl_then [`t0`,`t1`,`qu`] strip_assume_tac) 
               >> rfs [less_than_quota_def,Valid_CandTally_DEC2_def])));
    
 
  
val LogicalLessThanQu_IMP_less_than_quota =Q.store_thm ("LogicalLessThanQu_IMP_less_than_quota",
  `!(qu:rat) t h. (!c. (MEM c h) ==> ?x. (MEM (c,x) t) 
                                       /\ (x < qu)) /\ (!c'. NO_DUP_PRED (MAP FST t) c')
                                       /\ (!c''. (MEM c'' h) ==> (MEM c'' (MAP FST t)))
                                   ==> (less_than_quota qu h t)`,
  
   Induct_on `h`
     >- rw [less_than_quota_def]       
     >- (REPEAT STRIP_TAC  
       >> rw[less_than_quota_def] 
         >> `?x. (MEM (h',x) t) /\ (x < qu)` by metis_tac[MEM] 
           >> `MEM h' (MAP FST t)` by metis_tac[MEM] 
             >> `MEM (h', get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2] 
               >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY 
                 >> `get_cand_tally h' t = x` by rfs []
                   >> metis_tac []));  

 
     
val bigger_than_cand_def = Define `
           (bigger_than_cand c t [] = T)
        /\ (bigger_than_cand c t (h0::h1) = if (get_cand_tally c t) <= (get_cand_tally h0 t)
                                                then (bigger_than_cand c t h1)
                                             else F) `;     
    

val bigger_than_cand_OK = Q.store_thm ("bigger_than_cand_OK",
 `!c t h. (bigger_than_cand c t h) ==> (!d. (MEM d h) ==> (get_cand_tally c t <= get_cand_tally d t))`,

      Induct_on `h`
          >- rw []
          >- (REPEAT STRIP_TAC 
            >> FULL_SIMP_TAC list_ss [MEM,bigger_than_cand_def]));
    


val _ = Q.store_thm ("bigger_than_cand_IMP_LogicalBiggerThanCand",
 `!h (t0: Cand #rat) t1 c. (bigger_than_cand c (t0::t1) h) 
                        /\ (Valid_CandTally_DEC2 (t0::t1) h) /\ (MEM c h) ==>
   (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) (t0::t1)) /\ (MEM (d,y) (t0::t1)) /\ (x <= y)))`,  

     Induct_on `h`    
        >- rw []
        >- (REPEAT STRIP_TAC 
          >> ASSUME_TAC CandTally_DEC2_IMP_CandTally   
            >> first_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac) 
              >> `!c'. (MEM c' (h'::h)) ==> (MEM c' (MAP FST (t0::t1)))` by metis_tac []  
                >> first_assum (qspecl_then [`c`] strip_assume_tac) 
                  >> first_assum (qspecl_then [`d`] strip_assume_tac)  
                    >> `MEM (c,get_cand_tally c (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]   
                      >> `MEM (d,get_cand_tally d (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]   
                       >> MAP_EVERY qexists_tac [`get_cand_tally c (t0::t1)`,`get_cand_tally d (t0::t1)`] 
                         >> RW_TAC list_ss []  
                           >> ASSUME_TAC bigger_than_cand_OK 
                             >> first_assum (qspecl_then [`c`,`t0::t1`,`h'::h`] strip_assume_tac)    
                               >> metis_tac []));     
   

val _ = Q.store_thm ("LogicalBiggerThanCand_IMP_bigger_than_cand",
 `!h t c. (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) t) 
                                                  /\ (MEM (d,y) t) /\ (x <= y))) 
                                                  /\ (!d'. NO_DUP_PRED (MAP FST t) d')
                                                  /\ (MEM c (MAP FST t))
                                                  /\ (!d''. (MEM d'' h) ==> (MEM d'' (MAP FST t)))
                                                 ==> (bigger_than_cand c t h)`,

    Induct_on `h`
        >- rw [bigger_than_cand_def]
        >- (REPEAT STRIP_TAC  
             >> rw[bigger_than_cand_def]   
               >> `?x y. (MEM (c,x) t) /\ (MEM (h',y) t) /\ (x <= y) ` by metis_tac [MEM]   
                >> `MEM c (MAP FST t)` by metis_tac [MEM]
                 >> `MEM (c,get_cand_tally c t) t` by metis_tac [GET_CAND_TALLY_MEM2] 
                  >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY  
                   >> `x = get_cand_tally c t` by rfs []    
                    >> `MEM h' (MAP FST t)` by metis_tac [MEM]
                     >> `MEM (h',get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2] 
                      >> `y = get_cand_tally h' t ` by rfs [] 
                       >> RW_TAC bool_ss [])); 
 
     
 






          
val elim_cand_def = Define ` (elim_cand st (qu :rat) (l : Cand list) (c: Cand) j1 j2) = (?t p e h nh nba np.
    (j1 = state ([], t, p, [], e, h))
    /\ Valid_Init_CandList l
    /\ (!c'. (MEM c' h) \/ (MEM c' e) ==> (MEM c' l))
    /\ (!c'. NO_DUP_PRED h c')
    /\ (!c'. NO_DUP_PRED e c')
    /\ (LENGTH (e ++ h) > st) 
    /\ (LENGTH e < st)
    /\ (!c'. NO_DUP_PRED (MAP FST t) c')
    /\ Valid_CandTally t l
    /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))  
    /\ (MEM c h) 
    /\ (!d. (MEM d h ==> (?x y. (MEM (c,x) t) /\ (MEM (d,y) t) /\ ( x <= y))))
    /\ (eqe c nh h)
    /\ (nba = get_cand_pile c p)
    /\ ( MEM (c,[]) np)
    /\ (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p ==> MEM (d',l) np) 
                              /\ (MEM (d',l) np ==> MEM (d',l) p))))
    /\ (j2 = state (nba, t, np, [], e, nh)))) `; 
                  



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
                            
                       
val All_Tallies_Legal_def = Define `
                               (All_Tallies_Legal (l: Cand list) [] = T)    
                            /\ (All_Tallies_Legal l (h::t) = ((Legal_Tally_Cand l (h::t) (FST h)) 
                                                           /\ (All_Tallies_Legal l t))) `;

  
val Legal_Init_CandList = Define `Legal_Init_CandList l t = ((l <> []) /\ (MAP FST t = l))`;

    
`!l t. ((t <> []) /\ (All_Tallies_Legal l t = T)) ==> (!c. (MEM c l) ==> (Legal_Tally_Cand l t c = T)) `
        
 Induct_on `t`
 
   rw []
 
   REPEAT STRIP_TAC ASSUME_TAC CAND_EQ_DEC first_assum (qspecl_then [`c`,`FST h`] strip_assume_tac) 
   
        FULL_SIMP_TAC bool_ss [Legal_Tally_Cand_def,All_Tallies_Legal_def]  
    
        rw [Legal_Tally_Cand_def] FULL_SIMP_TAC bool_ss [All_Tallies_Legal_def]
        Induct_on `t`  
        
               rw [] 
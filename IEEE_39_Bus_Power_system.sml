(* ========================================================================= *)
(* File Name: IEEE 39 Bus Power System.sml	          	                                     *)
(*---------------------------------------------------------------------------*)
(*          Description: Formalization of cause-Consequence Diagrams for     *)
(*	    		 Safety Analysis in Higher-order Logic               *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Abdelghany             		     	     *)
(*                                              			     *)
(* 	    Department of Electrical and Computer Engineering (ECE)          *)
(*	    Concordia University                                             *)
(*          Montreal, Quebec, Canada, 2020                                   *)
(*                                                                           *)
(* ========================================================================= *)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "real_probabilityTheory",
	  "numTheory", "dep_rewrite", "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory","real_sigmaTheory",
	  "indexedListsTheory", "listLib", "bossLib", "metisLib", "realLib", "numLib", "combinTheory",
          "arithmeticTheory","boolTheory", "listSyntax", "lebesgueTheory",
	  "real_sigmaTheory", "cardinalTheory", "FT_deepTheory", "ETREETheory", "RBDTheory", "CDDTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax lebesgueTheory real_sigmaTheory cardinalTheory
     FT_deepTheory ETREETheory RBDTheory CDDTheory;

val _ = new_theory "IEEE_39_BUS_POWER_SYSTEM";

(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

	(*---------------------------------------------------------------------*)
     	(*   IEEE 39-Bus ELectrical Power Network CCD-Based Safety Analysis    *)
     	(*---------------------------------------------------------------------*)

(*------------------*)  
(*  Definitions     *)
(*------------------*)

val PV_PLANT_FAILURE_DEF = Define
`PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]  =
 FTree p (OR [OR (gate_list [LF1; DC_DC1; DC_AC1; SA1]);
              OR (gate_list [LF2; DC_DC2; DC_AC2; SA2])])`;

val STEAM_PLANT_FAILURE_DEF = Define
`STEAM_PLANT_FAILURE  p [BO1;BO2;BO3] [TA1;TA2;TA3] =
 FTree p (AND [AND (gate_list [BO1; TA1]);
               AND (gate_list [BO2; TA2]);
	       AND (gate_list [BO3; TA3])])`;

val BUS_INTERRUPTION_DEF = Define
`(BUS_INTERRUPTION [] [] [] p = 0) /\
 (BUS_INTERRUPTION  (X::Xs) (MTTR::MTTRs) (CN::CNs) p = 
 (prob p (CONSEQ_BOX p X)) * MTTR * CN + BUS_INTERRUPTION Xs MTTRs CNs p) `;

val SUM_REAL_DEF = Define
`(SUM_REAL [] = 0) /\
 (SUM_REAL (h::t) = (h:real) + SUM_REAL t)`;

val LIGHTNING  =  U 0x021AF;
val _ = Unicode.unicode_version {tmnm = "BUS_INTERRUPTION", u = SUM^T^LIGHTNING};

val SAIDI_DEF = Define
`SAIDI Xs MTTRs CNs p =  (BUS_INTERRUPTION Xs MTTRs CNs p) / SUM_REAL CNs`;
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------*)  
(*  SAIDI Theorems of Electrical Power Network       *)
(*---------------------------------------------------*)

val PV_PLANT_FAILURE_EQ_OR = store_thm("PV_PLANT_FAILURE_EQ_OR",
``!p LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2 .
PV_PLANT_FAILURE   p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]
  = FTree p (OR (gate_list [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1;SA2]))``,
rw [PV_PLANT_FAILURE_DEF]
\\ rw [FTree_def, gate_list_def]
\\ rw [INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PV_PLANT_FAILURE_IN_EVENTS = store_thm("PV_PLANT_FAILURE_IN_EVENTS",
``!LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2 p.
   prob_space p /\
   (∀y. MEM y [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1;SA2] ⇒ y ∈ events p) ==>
   PV_PLANT_FAILURE   p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]IN events p``,
rw [PV_PLANT_FAILURE_EQ_OR]
\\ DEP_REWRITE_TAC [FT_OR_IN_EVENTS]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val STEAM_PLANT_FAILURE_EQ_AND = store_thm("STEAM_PLANT_FAILURE_EQ_AND",
``! BO1 BO2 BO3 TA1 TA2 TA3 p.
  STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]  =
  FTree p (AND (gate_list [BO1;BO2;BO3; TA1;TA2;TA3])) ``,
rw [STEAM_PLANT_FAILURE_DEF]
\\ rw [FTree_def, gate_list_def]
\\ rw [INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val  STEAM_PLANT_FAILURE_IN_EVENTS = store_thm("STEAM_PLANT_FAILURE_IN_EVENTS",
``! BO1 BO2 BO3 TA1 TA2 TA3 p .  prob_space p /\
   (∀y. MEM y [BO1;BO2;BO3; TA1;TA2;TA3] ⇒ y ∈ events p)
   ==> STEAM_PLANT_FAILURE  p [BO1;BO2;BO3] [TA1;TA2;TA3] IN events p``,
rw [STEAM_PLANT_FAILURE_EQ_AND]
\\ DEP_REWRITE_TAC [FT_AND_IN_EVENTS]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val  LEMMA1 = store_thm("LEMMA1",
``!FT_R FT_R_BAR FT_T FT_T_BAR FT_F FT_F_BAR p. prob_space p /\
  (∀y. MEM y [FT_R; FT_R_BAR; FT_T; FT_T_BAR; FT_F; FT_F_BAR] ⇒ y ∈ events p) ==>
  CONSEQ_BOX p [[DECISION_BOX p 1 (FT_R_BAR, FT_R); DECISION_BOX p 2 (FT_T_BAR, FT_T);
                 DECISION_BOX p 2 (FT_F_BAR, FT_F)];
		[DECISION_BOX p 0 (FT_R_BAR, FT_R); DECISION_BOX p 1 (FT_T_BAR, FT_T);
                 DECISION_BOX p 2 (FT_F_BAR, FT_F)];
		[DECISION_BOX p 0 (FT_R_BAR, FT_R); DECISION_BOX p 0 (FT_T_BAR, FT_T);
                 DECISION_BOX p 1 (FT_F_BAR, FT_F)]] = 
  CONSEQ_BOX p [[DECISION_BOX p 1 (FT_R_BAR, FT_R)];
		[DECISION_BOX p 0 (FT_R_BAR, FT_R); DECISION_BOX p 1 (FT_T_BAR, FT_T)];
		[DECISION_BOX p 0 (FT_R_BAR, FT_R); DECISION_BOX p 0 (FT_T_BAR, FT_T);
                 DECISION_BOX p 1 (FT_F_BAR, FT_F)]]``,

rw [CONSEQ_BOX_DEF, CONSEQ_PATH_DEF, DECISION_BOX_DEF]
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ sg `FT_R_BAR ∩ p_space p ∩ p_space p =  FT_R_BAR`
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ sg `FT_R ∩ FT_T_BAR ∩ p_space p = FT_R ∩ FT_T_BAR`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_2_FAILURE = store_thm("PROB_CONSEQ_BOX_BUS_2_FAILURE",
``! p BO1 BO2 BO3 TA1 TA2 TA3.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] ))),
	        STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] ))),
	        STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] ))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] ))),
	        STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] ))),
	        STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]] /\

MUTUAL_INDEP p (compl_list p [BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] ⧺
                             [BO1; BO2; BO3; TA1; TA2; TA3] ⧺ [BO1; BO2; BO3; TA1; TA2; TA3]) /\
			     
(∀y. MEM y [BO1;BO2;BO3;TA1;TA2;TA3] ⇒ y ∈ events p) ==>

prob p (CONSEQ_BOX p
         [[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]]) =
	(1 −
         prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
        (prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) +
        prob p BO1 *
        (prob p BO2 *
         (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3)))) *
        (1 −
         prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3)))))``,
rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
\\ rw [PROB_SUM_DEF]
\\ sg `prob p
          (CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3] );
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p  [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p  [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
       (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))
       * ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])`
   >-( rw [STEAM_PLANT_FAILURE_EQ_AND]
       \\ rw [FTree_def]
       \\ rw [GSYM FTree_def]
       \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_10]
       \\ rw []
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p  [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
       ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])
       * (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))`
   >-( rw [STEAM_PLANT_FAILURE_EQ_AND]
       \\ rw [FTree_def]
       \\ rw [GSYM FTree_def]
       \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_01]
       \\ rw []
       \\ metis_tac [])
\\ POP_ORW
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_6_FAILURE = store_thm("PROB_CONSEQ_BOX_BUS_6_FAILURE",
``! p BO1 BO2 BO3 TA1 TA2 TA3 LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2] )];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]] /\

MUTUAL_INDEP p (compl_list p [BO1; BO2; BO3; TA1; TA2; TA3; LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] ++
               		[BO1; BO2; BO3; TA1; TA2; TA3] ++ [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]) /\

(∀y. MEM y [BO1;BO2;BO3; TA1;TA2;TA3; LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]  ⇒ y ∈ events p)
==>
prob p (CONSEQ_BOX p
           [[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2] )];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	      STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]]) =
	(1 −
         prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
        (1 −
         (1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) +
        prob p BO1 *
        (prob p BO2 *
         (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3)))) *
        ((1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))))``,

rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
\\ rw [PROB_SUM_DEF]
\\ sg `prob p
          (CONSEQ_PATH p
             [DECISION_BOX p 1
                (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
		STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
              DECISION_BOX p 0
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
		 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]) =
    (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))
    * (1 − ∏ (PROB_LIST p (compl_list p  [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])))`
    >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_10]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ sg `prob p
          (CONSEQ_PATH p
             [DECISION_BOX p 0
                (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
		STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
              DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
		 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]) =
    ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])
    * ∏ (PROB_LIST p (compl_list p [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]))`
     >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_01]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW     
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def, PROB_COMPL]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_28_FAILURE = store_thm("PROB_CONSEQ_BOX_BUS_28_FAILURE",
``! p LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (PV_PLANT_FAILURE  p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]] /\

MUTUAL_INDEP p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                              LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] ++
               		     [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] ++
			     [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]) /\
			     
(∀y. MEM y [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] ⇒ y ∈ events p)
==>
prob p (CONSEQ_BOX p 
  [[DECISION_BOX p 0
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
     DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])];
    [DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	         PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
     DECISION_BOX p 0 (
                FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]]) =
        (1 −
         (1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
        ((1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) +
        (1 − prob p LF1) *
        ((1 − prob p LF2) *
         ((1 − prob p DC_DC1) *
          ((1 − prob p DC_DC2) *
           ((1 − prob p DC_AC1) *
            ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))) *
        (1 −
         (1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))))``,

rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
\\ rw [PROB_SUM_DEF]
\\ sg `prob p
          (CONSEQ_PATH p
             [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2] ))),
		 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
              DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
		 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]) =
   (1 − ∏ (PROB_LIST p (compl_list p [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]))) *
   ∏ (PROB_LIST p (compl_list p [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]))`
    >-( rw [PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_01]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ sg `prob p
          (CONSEQ_PATH p
             [DECISION_BOX p 1
                (FTree p
                   (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
              DECISION_BOX p 0
                (FTree p
                   (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2])]) =
   ∏ (PROB_LIST p (compl_list p [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] )) *
   (1 - ∏ (PROB_LIST p (compl_list p [LF1; LF2 ; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])))`
     >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_10]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW     
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def, PROB_COMPL]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_16_FAILURE = store_thm("PROB_CONSEQ_BOX_BUS_16_FAILURE",
``! p BO1 BO2 BO3 TA1 TA2 TA3 LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]]) /\

ALL_DISTINCT
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
         CONSEQ_PATH p
           [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]] /\

MUTUAL_INDEP p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                              LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
			      BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] ++
			      [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] ++
                              [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]++
			      [BO1; BO2; BO3; TA1; TA2; TA3] ++ [BO1; BO2; BO3; TA1; TA2; TA3]) /\

(∀y. MEM y [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2; BO1; BO2; BO3; TA1; TA2; TA3] ⇒ y ∈ events p)
==>

prob p (CONSEQ_BOX p
         [[DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])];
           [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
	        PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);             
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
	       STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]]) =
             (1 − prob p LF1) *
        ((1 − prob p LF2) *
         ((1 − prob p DC_DC1) *
          ((1 − prob p DC_DC2) *
           ((1 − prob p DC_AC1) *
            ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))) *
        ((1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
        (1 −
         prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
        (prob p BO1 *
         (prob p BO2 *
          (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) +
        ((1 − prob p LF1) *
         ((1 − prob p LF2) *
          ((1 − prob p DC_DC1) *
           ((1 − prob p DC_DC2) *
            ((1 − prob p DC_AC1) *
             ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))) *
         ((1 − prob p LF1) *
          ((1 − prob p LF2) *
           ((1 − prob p DC_DC1) *
            ((1 − prob p DC_DC2) *
             ((1 − prob p DC_AC1) *
              ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
         (prob p BO1 *
          (prob p BO2 *
           (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
         (1 −
          prob p BO1 *
          (prob p BO2 *
           (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) +
         ((1 − prob p LF1) *
          ((1 − prob p LF2) *
           ((1 − prob p DC_DC1) *
            ((1 − prob p DC_DC2) *
             ((1 − prob p DC_AC1) *
              ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2))))))) *
          (1 −
           (1 − prob p LF1) *
           ((1 − prob p LF2) *
            ((1 − prob p DC_DC1) *
             ((1 − prob p DC_DC2) *
              ((1 − prob p DC_AC1) *
               ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
          (1 −
           prob p BO1 *
           (prob p BO2 *
            (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
          (1 −
           prob p BO1 *
           (prob p BO2 *
            (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) +
          (1 −
           (1 − prob p LF1) *
           ((1 − prob p LF2) *
            ((1 − prob p DC_DC1) *
             ((1 − prob p DC_DC2) *
              ((1 − prob p DC_AC1) *
               ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
          ((1 − prob p LF1) *
           ((1 − prob p LF2) *
            ((1 − prob p DC_DC1) *
             ((1 − prob p DC_DC2) *
              ((1 − prob p DC_AC1) *
               ((1 − prob p DC_AC2) * ((1 − prob p SA1) * (1 − prob p SA2)))))))) *
          (1 −
           prob p BO1 *
           (prob p BO2 *
            (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3))))) *
          (1 −
           prob p BO1 *
           (prob p BO2 *
            (prob p BO3 * (prob p TA1 * (prob p TA2 * prob p TA3)))))))``,

rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])
   >-( rw [CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, DECISION_BOX_DEF, FTree_def]
       \\ DEP_REWRITE_TAC [STEAM_PLANT_FAILURE_IN_EVENTS, PV_PLANT_FAILURE_IN_EVENTS,
                           EVENTS_COMPL, EVENTS_INTER]
       \\ rw []
       \\ metis_tac [])

\\ rw [PROB_SUM_DEF]
\\ sg `prob p
          (CONSEQ_PATH p
             [DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
              DECISION_BOX p 1
                (FTree p (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                 PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
              DECISION_BOX p 1
                (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                 STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
              DECISION_BOX p 0
                (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                 STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
     ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
     ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
     (1 -∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])) *
      ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])`
    >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [FOUR_DECISION_BOXES_1110]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ sg `prob p
           (CONSEQ_PATH p
              [DECISION_BOX p 1
                 (FTree p
                    (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                  PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2] );
               DECISION_BOX p 1
                 (FTree p
                    (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                  PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
               DECISION_BOX p 0
                 (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                  STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
               DECISION_BOX p 1
                 (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                  STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
     ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
     ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
     ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]) *
     (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))`
    >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [FOUR_DECISION_BOXES_1101]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ sg `prob p
            (CONSEQ_PATH p
               [DECISION_BOX p 1
                  (FTree p
                     (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                   PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
                DECISION_BOX p 0
                  (FTree p
                     (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                   PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
                DECISION_BOX p 1
                  (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                   STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
                DECISION_BOX p 1
                  (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                   STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
  ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
 (1 - ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]))) *
 (1 - ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])) *
 (1 - ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))`
    >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [FOUR_DECISION_BOXES_1011]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ sg `prob p
            (CONSEQ_PATH p
               [DECISION_BOX p 0
                  (FTree p
                     (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                   PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
                DECISION_BOX p 1
                  (FTree p
                     (NOT (atomic (PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]))),
                   PV_PLANT_FAILURE p [LF1; LF2] [DC_DC1; DC_DC2] [DC_AC1; DC_AC2] [SA1;SA2]);
                DECISION_BOX p 1
                  (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                   STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]);
                DECISION_BOX p 1
                  (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3]))),
                   STEAM_PLANT_FAILURE p [BO1;BO2;BO3] [TA1;TA2;TA3])]) =
 (1 - ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]))) *
  ∏ (PROB_LIST p (compl_list p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2])) *
  (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3])) *
  (1 − ∏ (PROB_LIST p [BO1;BO2;BO3;TA1;TA2;TA3]))`
    >-( rw [STEAM_PLANT_FAILURE_EQ_AND, PV_PLANT_FAILURE_EQ_OR] 
        \\ rw [FTree_def]
        \\ rw [GSYM FTree_def]
        \\ DEP_REWRITE_TAC [FOUR_DECISION_BOXES_0111]
        \\ rw []
        \\ metis_tac [])     
\\ POP_ORW
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def, PROB_COMPL]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_2_FAILURE_DISTIBUTION = store_thm("PROB_CONSEQ_BOX_BUS_2_FAILURE_DISTIBUTION",

``! p BO1 BO2 BO3 TA1 TA2 TA3 t.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]] /\
	      
MUTUAL_INDEP p (compl_list p (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] t) ⧺
                             (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ⧺
			     (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t)) /\
			     
(∀y. MEM y (FAIL_LIST p [BO1;BO2;BO3;TA1;TA2;TA3] t) ⇒ y ∈ events p) ==>

prob p (CONSEQ_BOX p
         [[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) =
       (1 −
         prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
        (prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) +
        prob p (↓ p BO1 t) *
        (prob p (↓ p BO2 t) *
         (prob p (↓ p BO3 t) *
          (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t))))) *
        (1 −
         prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t))))))``,
rw [FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_2_FAILURE]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_6_FAILURE_DISTRIBUTION = store_thm("PROB_CONSEQ_BOX_BUS_6_FAILURE_DISTRIBUTION",
``! p BO1 BO2 BO3 TA1 TA2 TA3 LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2 t.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]] /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; LF1; LF2; DC_DC1;
                                           DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
               		     (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)) /\

(∀y. MEM y (FAIL_LIST p [BO1;BO2;BO3; TA1;TA2;TA3; LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)
 ⇒ y ∈ events p) ==>
prob p (CONSEQ_BOX p
           [[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) =

        (1 −
         prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
        (1 −
         (1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) +
        prob p (↓ p BO1 t) *
        (prob p (↓ p BO2 t) *
         (prob p (↓ p BO3 t) *
          (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t))))) *
        ((1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))))``,

rw [FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_6_FAILURE]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_28_FAILURE_DISTRIBUTION = store_thm("PROB_CONSEQ_BOX_BUS_28_FAILURE_DISTRIBUTION",
``! p LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2 t.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]] /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                                           LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
               		     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
			     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)) /\
			     
(∀y. MEM y (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ⇒ y ∈ events p)
==>
prob p (CONSEQ_BOX p
  [[DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
     DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
     DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) =

        (1 −
         (1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
        ((1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) +
        (1 − prob p (↓ p LF1 t)) *
        ((1 − prob p (↓ p LF2 t)) *
         ((1 − prob p (↓ p DC_DC1 t)) *
          ((1 − prob p (↓ p DC_DC2 t)) *
           ((1 − prob p (↓ p DC_AC1 t)) *
            ((1 − prob p (↓ p DC_AC2 t)) *
             ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))) *
        (1 −
         (1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))))``,

rw [FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_28_FAILURE]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val  PROB_CONSEQ_BOX_BUS_16_FAILURE_DISTRIBUTION = store_thm("PROB_CONSEQ_BOX_BUS_16_FAILURE_DISTRIBUTION",
``! p BO1 BO2 BO3 TA1 TA2 TA3 LF1 LF2 DC_DC1 DC_DC2 DC_AC1 DC_AC2 SA1 SA2 t.  prob_space p /\ 
disjoint (set
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	   [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
           DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	   [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
           DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]] /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                                           LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
			                   BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			      (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
                              (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
			      (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			      (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t)) /\

(∀y. MEM y (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2;
                         SA1; SA2; BO1; BO2; BO3; TA1; TA2; TA3] t) ⇒ y ∈ events p) ==>

prob p (CONSEQ_BOX p
         [[DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
	   [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
           DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) =

        (1 − prob p (↓ p LF1 t)) *
        ((1 − prob p (↓ p LF2 t)) *
         ((1 − prob p (↓ p DC_DC1 t)) *
          ((1 − prob p (↓ p DC_DC2 t)) *
           ((1 − prob p (↓ p DC_AC1 t)) *
            ((1 − prob p (↓ p DC_AC2 t)) *
             ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))) *
        ((1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
        (1 −
         prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
        (prob p (↓ p BO1 t) *
         (prob p (↓ p BO2 t) *
          (prob p (↓ p BO3 t) *
           (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) +
        ((1 − prob p (↓ p LF1 t)) *
         ((1 − prob p (↓ p LF2 t)) *
          ((1 − prob p (↓ p DC_DC1 t)) *
           ((1 − prob p (↓ p DC_DC2 t)) *
            ((1 − prob p (↓ p DC_AC1 t)) *
             ((1 − prob p (↓ p DC_AC2 t)) *
              ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))) *
         ((1 − prob p (↓ p LF1 t)) *
          ((1 − prob p (↓ p LF2 t)) *
           ((1 − prob p (↓ p DC_DC1 t)) *
            ((1 − prob p (↓ p DC_DC2 t)) *
             ((1 − prob p (↓ p DC_AC1 t)) *
              ((1 − prob p (↓ p DC_AC2 t)) *
               ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
         (prob p (↓ p BO1 t) *
          (prob p (↓ p BO2 t) *
           (prob p (↓ p BO3 t) *
            (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
         (1 −
          prob p (↓ p BO1 t) *
          (prob p (↓ p BO2 t) *
           (prob p (↓ p BO3 t) *
            (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) +
         ((1 − prob p (↓ p LF1 t)) *
          ((1 − prob p (↓ p LF2 t)) *
           ((1 − prob p (↓ p DC_DC1 t)) *
            ((1 − prob p (↓ p DC_DC2 t)) *
             ((1 − prob p (↓ p DC_AC1 t)) *
              ((1 − prob p (↓ p DC_AC2 t)) *
               ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t)))))))) *
          (1 −
           (1 − prob p (↓ p LF1 t)) *
           ((1 − prob p (↓ p LF2 t)) *
            ((1 − prob p (↓ p DC_DC1 t)) *
             ((1 − prob p (↓ p DC_DC2 t)) *
              ((1 − prob p (↓ p DC_AC1 t)) *
               ((1 − prob p (↓ p DC_AC2 t)) *
                ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
          (1 −
           prob p (↓ p BO1 t) *
           (prob p (↓ p BO2 t) *
            (prob p (↓ p BO3 t) *
             (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
          (1 −
           prob p (↓ p BO1 t) *
           (prob p (↓ p BO2 t) *
            (prob p (↓ p BO3 t) *
             (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) +
          (1 −
           (1 − prob p (↓ p LF1 t)) *
           ((1 − prob p (↓ p LF2 t)) *
            ((1 − prob p (↓ p DC_DC1 t)) *
             ((1 − prob p (↓ p DC_DC2 t)) *
              ((1 − prob p (↓ p DC_AC1 t)) *
               ((1 − prob p (↓ p DC_AC2 t)) *
                ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
          ((1 − prob p (↓ p LF1 t)) *
           ((1 − prob p (↓ p LF2 t)) *
            ((1 − prob p (↓ p DC_DC1 t)) *
             ((1 − prob p (↓ p DC_DC2 t)) *
              ((1 − prob p (↓ p DC_AC1 t)) *
               ((1 − prob p (↓ p DC_AC2 t)) *
                ((1 − prob p (↓ p SA1 t)) * (1 − prob p (↓ p SA2 t))))))))) *
          (1 −
           prob p (↓ p BO1 t) *
           (prob p (↓ p BO2 t) *
            (prob p (↓ p BO3 t) *
             (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t)))))) *
          (1 −
           prob p (↓ p BO1 t) *
           (prob p (↓ p BO2 t) *
            (prob p (↓ p BO3 t) *
             (prob p (↓ p TA1 t) * (prob p (↓ p TA2 t) * prob p (↓ p TA3 t))))))))``,

rw [FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_16_FAILURE]
\\ rw []
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------*)  
(*  SAIDI Expression Validation     *)
(*----------------------------------*)

val  SAIDI_EXPRESSION_VALIDATION = store_thm("SAIDI_EXPRESSION_VALIDATION",
``!p BO1  TA1 BO2  TA2  BO3  TA3 LF1 DC_DC1 DC_AC1 SA1 LF2 DC_DC2 DC_AC2 SA2 
   MTTR_B2 MTTR_B6 MTTR_B16 MTTR_B28 CN_B2 CN_B6 CN_B16 CN_B28 FR_BO1 FR_BO2 FR_BO3 FR_TA1 FR_TA2
   FR_TA3 FR_LF1 FR_LF2 FR_DC_DC1 FR_DC_DC2 FR_DC_AC1 FR_DC_AC2 FR_SA1 FR_SA2 t.

disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	        STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
            (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                 (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]] /\

disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]] /\
disjoint (set
         [CONSEQ_PATH p
            [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
            [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
          CONSEQ_PATH p
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]] /\
disjoint (set
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	   [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
           DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]) /\
ALL_DISTINCT
         [CONSEQ_PATH p
           [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
         CONSEQ_PATH p
	   [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
           DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]] /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; LF1; LF2; DC_DC1;
                                           DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
               		     (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)) /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                                           LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
			                   BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			      (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
                              (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
			      (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ++
			      (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t)) /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2;
                                           LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
               		     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t) ++
			     (FAIL_LIST p [LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)) /\

MUTUAL_INDEP p (compl_list p (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; BO1; BO2; BO3; TA1; TA2; TA3] t) ⧺
                             (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t) ⧺
			     (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3] t)) /\
			     
(∀y. MEM y (FAIL_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2] t)
 ⇒ y ∈ events p) /\ prob_space p /\ 0 <= t /\

  EXP_ET_DISTRIB_LIST p [BO1; BO2; BO3; TA1; TA2; TA3; LF1; LF2; DC_DC1; DC_DC2; DC_AC1; DC_AC2; SA1; SA2]
                        [FR_BO1; FR_BO2; FR_BO3; FR_TA1; FR_TA2; FR_TA3; FR_LF1;
		         FR_LF2; FR_DC_DC1; FR_DC_DC2; FR_DC_AC1; FR_DC_AC2; FR_SA1; FR_SA2] ==> 
  
SAIDI 
          [[[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]];
        [[DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
            [DECISION_BOX p 0
              (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                   (FAIL_LIST p [TA1;TA2;TA3] t)))),
	      STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]];
         [[DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))];
            [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
             DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t))]];
         [[DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));	
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))];            
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
	    [DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]; 
	    [DECISION_BOX p 0
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t)))),
	                              PV_PLANT_FAILURE p (FAIL_LIST p [LF1; LF2] t)
	                                                 (FAIL_LIST p [DC_DC1; DC_DC2] t)
							 (FAIL_LIST p [DC_AC1; DC_AC2]t)
							 (FAIL_LIST p [SA1;SA2] t));
            DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t));            
	    DECISION_BOX p 1
               (FTree p (NOT (atomic (STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t)
	                                                    (FAIL_LIST p [TA1;TA2;TA3] t)))),
	       STEAM_PLANT_FAILURE p (FAIL_LIST p [BO1;BO2;BO3] t) (FAIL_LIST p [TA1;TA2;TA3] t))]]]
	       
[MTTR_B2; MTTR_B6; MTTR_B16; MTTR_B28] [CN_B2; CN_B6; CN_B16; CN_B28] p =

        (((1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          ((1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) +
          (1 − exp (-FR_BO1 * t)) *
          ((1 − exp (-FR_BO2 * t)) *
           ((1 − exp (-FR_BO3 * t)) *
            ((1 − exp (-FR_TA1 * t)) *
             ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t)))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t)))))))) *
         MTTR_B2 * CN_B2 +
         ((1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          (1 −
           exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) +
          (1 − exp (-FR_BO1 * t)) *
          ((1 − exp (-FR_BO2 * t)) *
           ((1 − exp (-FR_BO3 * t)) *
            ((1 − exp (-FR_TA1 * t)) *
             ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t)))))) *
          (exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))))) * MTTR_B6 *
         CN_B6 +
         ((1 −
           exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          (exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) +
          exp (-FR_LF1 * t) *
          (exp (-FR_LF2 * t) *
           (exp (-FR_DC_DC1 * t) *
            (exp (-FR_DC_DC2 * t) *
             (exp (-FR_DC_AC1 * t) *
              (exp (-FR_DC_AC2 * t) *
               (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))) *
          (1 −
           exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))))) * MTTR_B16 *
         CN_B16 +
         (exp (-FR_LF1 * t) *
          (exp (-FR_LF2 * t) *
           (exp (-FR_DC_DC1 * t) *
            (exp (-FR_DC_DC2 * t) *
             (exp (-FR_DC_AC1 * t) *
              (exp (-FR_DC_AC2 * t) *
               (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))) *
          (exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          ((1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) +
          exp (-FR_LF1 * t) *
          (exp (-FR_LF2 * t) *
           (exp (-FR_DC_DC1 * t) *
            (exp (-FR_DC_DC2 * t) *
             (exp (-FR_DC_AC1 * t) *
              (exp (-FR_DC_AC2 * t) *
               (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))) *
          (exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          ((1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) +
          exp (-FR_LF1 * t) *
          (exp (-FR_LF2 * t) *
           (exp (-FR_DC_DC1 * t) *
            (exp (-FR_DC_DC2 * t) *
             (exp (-FR_DC_AC1 * t) *
              (exp (-FR_DC_AC2 * t) *
               (exp (-FR_SA1 * t) * exp (-FR_SA2 * t))))))) *
          (1 −
           exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) +
          (1 −
           exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          (exp (-FR_LF1 * t) *
           (exp (-FR_LF2 * t) *
            (exp (-FR_DC_DC1 * t) *
             (exp (-FR_DC_DC2 * t) *
              (exp (-FR_DC_AC1 * t) *
               (exp (-FR_DC_AC2 * t) *
                (exp (-FR_SA1 * t) * exp (-FR_SA2 * t)))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t))))))) *
          (1 −
           (1 − exp (-FR_BO1 * t)) *
           ((1 − exp (-FR_BO2 * t)) *
            ((1 − exp (-FR_BO3 * t)) *
             ((1 − exp (-FR_TA1 * t)) *
              ((1 − exp (-FR_TA2 * t)) * (1 − exp (-FR_TA3 * t)))))))) *
         MTTR_B28 * CN_B28) / (CN_B2 + CN_B6 + CN_B16 + CN_B28)``,

rw [SAIDI_DEF, BUS_INTERRUPTION_DEF, EXP_ET_DISTRIB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_2_FAILURE_DISTIBUTION]
\\ rw []
   >-(fs [FAIL_LIST_DEF])
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_6_FAILURE_DISTRIBUTION]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_16_FAILURE_DISTRIBUTION]
\\ rw []
   >-(fs [FAIL_LIST_DEF])
\\ DEP_REWRITE_TAC [PROB_CONSEQ_BOX_BUS_28_FAILURE_DISTRIBUTION]
\\ rw []
   >-(fs [FAIL_LIST_DEF])
\\ rw [SUM_REAL_DEF]
\\ rw [FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_SUB2]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------*)  
(*  SAIDI Expression Evaluation     *)
(*----------------------------------*)

(*----------------------------------------*)   
(* Assume  FR_BO1     =   0.44 per year   *)
(* Assume  FR_BO2     =   0.44 per year   *)
(* Assume  FR_BO3     =   0.44 per year   *)
(* Assume  FR_TA1     =   0.10 per year   *)
(* Assume  FR_TA2     =   0.10 per year   *)
(* Assume  FR_TA3     =   0.10 per year   *)
(* Assume  FR_LF1     =   0.96 per year   *)
(* Assume  FR_LF2     =   0.96 per year   *)
(* Assume  FR_DC_DC1  =   0.67 per year   *)
(* Assume  FR_DC_DC2  =   0.67 per year   *)
(* Assume  FR_DC_AC1  =   0.22 per year   *)
(* Assume  FR_DC_AC2  =   0.22 per year   *)
(* Assume  FR_SA1     =   0.56 per year   *)
(* Assume  FR_SA2     =   0.56 per year   *)
(* Assume  MTTR_B2    =   12 Hours        *)
(* Assume  MTTR_B6    =   20 Hours        *)
(* Assume  MTTR_B16   =   15 Hours        *)
(* Assume  MTTR_B28   =   10 Hour         *)
(* Assume  CN_B2      =  500 Customers    *)
(* Assume  CN_B6      =  1800 Customers   *)
(* Assume  CN_B16     =  900 Customers    *)
(* Assume  CN_B28     =  2500 Customers   *)
(*----------------------------------------*)

SAIDI``(((1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          ((1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) +
          (1 − exp (-(44:real)/(100:real))) *
          ((1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(10:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real))))))))) *
         (12:real) * (500:real) +
         ((1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          (1 −
           exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) +
          (1 − exp (-(44:real)/(100:real))) *
          ((1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(10:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real))))))) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))))) * (20:real) * (1800:real) +
         ((1 −
           exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) +
          exp (-(96:real)/(100:real)) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(67:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(22:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))) *
          (1 −
           exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))))) * (15:real) * (900:real) +
         (exp (-(96:real)/(100:real)) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(67:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(22:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          ((1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) +
          exp (-(96:real)/(100:real)) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(67:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(22:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          ((1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) +
          exp (-(96:real)/(100:real)) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(67:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(22:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real)))))))) *
          (1 −
           exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) +
          (1 −
           exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          (exp (-(96:real)/(100:real)) *
           (exp (-(96:real)/(100:real)) *
            (exp (-(67:real)/(100:real)) *
             (exp (-(67:real)/(100:real)) *
              (exp (-(22:real)/(100:real)) *
               (exp (-(22:real)/(100:real)) *
                (exp (-(56:real)/ (100:real)) * exp (-(56:real)/ (100:real))))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real)))))))) *
          (1 −
           (1 − exp (-(44:real)/(100:real))) *
           ((1 − exp (-(44:real)/(100:real))) *
            ((1 − exp (-(44:real)/(100:real))) *
             ((1 − exp (-(10:real)/(100:real))) *
              ((1 − exp (-(10:real)/(100:real))) * (1 − exp (-(10:real)/(100:real))))))))) *
          (10:real) * (2500:real)) / ((500:real) + ((1800:real) + ((900:real) + (2500:real))))``;	      


val _ = export_theory();

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
	(*------------------------------------------------------------------------------*)
		       (*--------------------------------------------------*)
			         (*--------------------------------*)
					  (*---------------*)
						********



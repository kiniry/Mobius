/*
 * Created on Feb 23, 2005
 */
package coqPlugin.printers;

import java.io.File;
import java.io.PrintStream;

import jml2b.IJml2bConfiguration;

import coqPlugin.PreferencePage;

/**
 * @author jcharles
 */
public class LocalTactics extends Printer {

	public static final String fileName ="jack_tactics";
	public LocalTactics(File output_directory, IJml2bConfiguration config) {
		super(output_directory, fileName + ".v");
		startWriting(config);
	}
	
	public boolean mustRewrite() {
		return true;
	}
	
	protected void writeToFile(PrintStream stream, IJml2bConfiguration config){
		stream.println("(* I am the third little helper. *)\n");
		stream.println("(** * The Local Tactics Library *)\n");
		stream.println("Open Scope J_Scope.");
/*		stream.println("Ltac elimAnd :=\n" +
		"	  repeat match goal with\n" +
		"	  | [H : _ /\\ _ |- _ ] =>\n" +
		"	     case H;clear H;\n" +
		"	     let H1 := fresh \"H\" in\n" +
		"	     let H2 := fresh \"H\" in\n" +
		"	     intros H1 H2\n" +
		"	  | [|- _ /\\ _] => split\n" +
		"	  end.\n"); */
		elimAnd(stream);
		rewrite_all(stream);
		solveInc(stream);
		elimOr(stream);
		elimif(stream);
		arrayTacs(stream);
		cleanup(stream);
		absurd(stream);
		macros(stream);
		automatic(stream);
		destrJle(stream);
		arrtac(stream);
		purity(stream);
		pattern_right (stream);
			
	} 
	
	



	/**
	 * uses: nothing
	 * provides: solveInc
	 * @param stream
	 */
	public void solveInc(PrintStream stream) {
		stream.println("(** ** SolveInc\n" +
			"SolveInc was once used to solve trivial incrementations and\n" +
			"some arithmetic stuff; it is a bit like a light j_omega\n\n" +
			"*)");
		stream.println("Lemma j_le_inc_sup : forall n m v, (Zle 0 n) -> (j_le m v) -> (j_le m (j_add v n)).\n" +
				   "Proof with auto.\n"+
				   "unfold j_le, j_add in *; intros.\n"+
				   "replace m with (((m - n)+ n)%Z).\n"+
				   "apply Zplus_le_compat_r. assert (((m - n) <= m)%Z).\n"+
				   "omega.\n"+
				   "apply Zle_trans with m...\n"+
				   "omega.\n"+
				   "Qed.\n");
	stream.println("Lemma j_le_inc_inf : forall m v, (j_lt v m) -> (j_le (j_add v 1) m).\n"+
					"Proof with auto.\n" +
					"unfold j_le, j_lt, j_add  in *; intros.\n"+
					"replace (v  + 1)%Z with (Zsucc v). apply Zlt_le_succ...\n" +
					"omega.\n" +
					"Qed.\n");
	stream.println("Lemma j_ge_le: forall n m, (j_le m n) -> (j_ge n m).\n" +
				   "Proof with auto.\n"+
				   "unfold j_ge, j_le; intros.\n"+
				   "apply Zle_ge...\n"+
				   "Qed.\n"); 
	stream.println("Lemma j_le_ge: forall n m, (j_ge m n) -> (j_le n m).\n"+
				   "Proof with auto.\n"+
			 	   "unfold j_ge, j_le; intros.\n"+
				   "apply Zge_le...\n"+
				   "Qed.\n");
	stream.println("Lemma j_gt_lt: forall n m, (j_lt m n) -> (j_gt n m).\n" +
			   "Proof with auto.\n"+
			   "unfold j_gt, j_lt; intros.\n"+
			   "apply Zlt_gt...\n"+
			   "Qed.\n"); 
	stream.println("Lemma j_lt_gt: forall n m, (j_gt m n) -> (j_lt n m).\n"+
			   "Proof with auto.\n"+
		 	   "unfold j_gt, j_lt; intros.\n"+
			   "apply Zgt_lt...\n"+
			   "Qed.\n");
	stream.println("Lemma j_not_gt_hyp: forall n m, (~ (j_gt m n)) -> (j_le m n).\n"
			+"Proof with auto.\n"
			+"unfold j_gt, j_le; intros; apply Znot_gt_le...\n"
			+"Qed.\n"
			+"Lemma j_not_gt: forall n m, (j_le m n) -> (~ (j_gt m n)).\n"
			+"Proof with auto.\n"
			+"unfold j_gt, j_le; intros; apply Zle_not_gt...\n"
			+"Qed.\n"
			+"Lemma j_not_ge_hyp: forall n m, (~ (j_ge m n)) -> (j_lt m n).\n"
			+"Proof with auto.\n"
			+"unfold j_ge, j_lt; intros; apply Znot_ge_lt...\n"
			+"Qed.\n"
			+"Lemma j_not_ge: forall n m, (j_lt m n) -> (~ (j_ge m n)).\n"
			+"Proof with auto.\n"
			+"unfold j_ge, j_lt.\n"
			+"intros n m H1 H2.  apply H2. assumption.\n"
			+"Qed. \n");
	
	stream.println("Lemma j_not_lt_hyp: forall n m, (~ (j_lt m n)) -> (j_ge m n).\n"
			+"Proof with auto.\n"
			+"unfold j_lt, j_ge; intros; apply Znot_lt_ge...\n"
			+"Qed.\n"
			+"Lemma j_not_lt: forall n m, (j_ge m n) -> (~ (j_lt m n)).\n"
			+"Proof with auto.\n"
			+"unfold j_lt, j_ge; intros n m H1 H2; apply H1; assumption.\n"
			+"Qed.\n"
			+"Lemma j_not_le_hyp: forall n m, (~ (j_le m n)) -> (j_gt m n).\n"
			+"Proof with auto.\n"
			+"unfold j_le, j_gt; intros; apply Znot_le_gt...\n"
			+"Qed.\n"
			+"Lemma j_not_le: forall n m, (j_gt m n) -> (~ (j_le m n)).\n"
			+"Proof with auto.\n"
			+"unfold j_le, j_gt; intros n m H1 H2.  apply H2. assumption.\n"
			+"Qed.\n");
	stream.println("Lemma j_le_dec_sup : forall m v, (j_lt m v) -> (j_le (j_sub v 1) m) -> m = (j_sub v 1).\n"+
			"Proof with auto.\n"+
			"unfold j_le, j_lt, j_sub  in *; intros m v h1 h2.\n"+
			"assert (h3:(v <= m + 1)%Z).\n"+
			"rewrite <- (Zplus_0_r v). rewrite <- (Zplus_opp_l 1). rewrite Zplus_assoc.\n"+
			"apply Zplus_le_compat_r. assumption.\n"+
			"replace (m  + 1)%Z with (Zsucc m) in h3.\n"+ 
			"assert(h4 : (Zsucc m <= v)%Z).\n"+
			"apply Zlt_le_succ...\n"+
			"apply Zle_antisym; omega. omega.\n"+ 
			"Qed.");
	stream.println("Ltac solve_hyp f t H m n :=\n"+ 
			"let H1 := fresh \"H\" in (assert (H1: f m n) ; [(apply t; assumption; clear H)|clear H]).\n");
	stream.println("Ltac solveInc :=\n" +
			"repeat match goal with \n" +
			//"|  [H: (j_le ?v ?w) |- (j_le ?v (j_add ?w _))] => apply j_le_inc_sup\n" +
			"|  [H: (j_lt ?v ?w) |- (j_le (j_add ?v 1) ?w)] => apply j_le_inc_inf;apply H\n" +
			"|  [H1: (j_le ?m ?n), H2: j_le ?n  ?m |- _] => \n" +
			"                      let H := fresh \"H\" in (assert (H: m = n); \n" +
			"                         [(apply Zle_antisym; auto; clear H1; clear H2) | (clear H1; clear H2)])\n" +
			"|  [H: (j_ge ?n ?m) |- _] => solve_hyp j_le j_le_ge H m n\n" +
			"|  [H: _ |- (j_ge ?n ?m)] => apply j_ge_le\n"+
			"|  [H: (j_gt ?n ?m) |- _] => solve_hyp j_lt j_lt_gt H m n\n" +
			"|  [H: _ |- (j_gt ?n ?m)] => apply j_gt_lt\n"+
			"|  [H: ~ (j_gt ?n ?m) |- _] => solve_hyp j_le j_not_gt_hyp H n m\n"+
			"|  [H: _ |- ~ (j_gt ?n ?m)] => apply j_not_gt\n"+
			"|  [H: ~ (j_ge ?n ?m) |- _] => solve_hyp j_lt j_not_ge_hyp H n m\n"+
			"|  [H: _ |- ~ (j_ge ?n ?m)] => apply j_not_ge\n"+
			"|  [H: ~ (j_lt ?n ?m) |- _] => solve_hyp j_ge j_not_lt_hyp H n m\n"+
			"|  [H: _ |- ~ (j_lt ?n ?m)] => apply j_not_lt\n"+
			"|  [H: ~ (j_le ?n ?m) |- _] => solve_hyp j_gt j_not_le_hyp H n m\n"+
			"|  [H: _ |- ~ (j_le ?n ?m)] => apply j_not_le\n" +
			"|  [H: _ |- j_le ?n ?n] => unfold j_le; apply Zle_refl\n" + 
			//"|  [H: _ |- (?a <= ?b)%Z] => omega\n"+
			"end.\n");		
	}


	/**
	 * uses: nothing
	 * provides: elimAnd
	 * @param s
	 */
	public void elimAnd(PrintStream s) {
		s.println("(**\n" +
		" ** elimAnd\n" +  
		" elimAnd is used mainly to eliminate and within the hypothesis.\n" +
		"For the goals the preferred tactic is still split.\n\n" +
		"*)\n");

		s.println("Ltac genclear H := generalize H;clear H.\n" +
				"Ltac map_hyp Tac :=\n"+
				"  repeat match goal with\n"+
				"    | [ H : _ |- _ ] => try (Tac H);genclear H\n"+
				"    end; intros.\n\n"+

				"Inductive Plist : Prop :=\n"+ 
				"  | Pnil : Plist\n"+
				"  | Pcons : Prop -> Plist -> Plist.\n\n"+

				"Ltac build_imp Pl C :=\n"+
				"  match Pl with\n"+
				"  | Pnil => constr:C\n"+
				"  | Pcons ?A ?Pl' =>\n"+ 
				"        let C' := constr:(A->C) in\n"+
				"        build_imp Pl' C'\n"+
				"  end.\n\n"+


					"Inductive PPlProd : Prop :=\n" +
					" | PPlPair : Plist -> Prop -> PPlProd.\n\n"+

					"Ltac elim_aT Pl T :=\n"+
					"  match T with\n"+
					"  | ?A /\\ ?B =>\n"+
					"      let A' := elim_aT Pl A in\n"+
					"      let B' := elim_aT Pl B in\n"+
					"      constr:(A' /\\ B')\n"+
					"  | ?A => build_imp Pl T\n"+
					"  end.\n\n"+ 

					"Ltac elim_iaT Pl T :=\n"+
					"   match T with\n"+
					"   | (?B /\\ ?C) =>\n"+ 
					"        let P := elim_aT Pl T in\n" +
					"        constr:(PPlPair Pl P)\n"+
					"   | (?A -> ?D) =>\n"+
					"        let Pl' := constr:(Pcons A Pl) in\n"+
					"        elim_iaT Pl' D\n"+
					"   end.\n\n"+

					"Ltac splitAndH H :=\n" +
					"  match type of H with\n"+
					"  | ?A /\\ ?B =>\n" +
					"             case H;clear H;\n"+
					"	     let H1 := fresh \"H\" in\n" +
					"	     let H2 := fresh \"H\" in\n"+
					"	     (intros H1 H2; splitAndH H1; splitAndH H2)\n"+
					"  | _ => idtac\n"+
					"  end.\n\n"+

					"Ltac introPl Pl H := \n"+
					" match Pl with\n"+
					" | Pnil => splitAndH H\n"+
					" | Pcons _ ?pl => \n"+
					"     let H1 := fresh \"H\" in\n"+
					"     let H2 := fresh \"H\" in \n"+
					"     (intro H1;assert (H2 := H H1);introPl pl H2)\n"+
					" end.\n\n"+

					"Ltac splitAnd := \n"+
					"  match goal with\n"+
					"  | [|- ?A /\\ ?B] => split;splitAnd\n"+
					"  | _ => idtac\n"+
					"  end.\n\n"+

					"Ltac elimAnd :=\n"+
					"  match goal with\n"+
					"  | [H : ? A /\\ ?B |- _ ] =>\n"+ 	    
					"             case H;clear H;\n"+
					"	     let H1 := fresh \"H\" in\n"+
					"	     let H2 := fresh \"H\" in\n"+
					"	     intros H1 H2; elimAnd\n"+
					"  | [H : ?HT|- _ ] =>\n"+
					"       let pair := elim_iaT Pnil HT in\n"+
					"       match pair with\n"+
					"       | PPlPair ?Pl ?newT =>\n"+
					"         assert newT;\n"+
					"         [splitAnd; introPl Pl H;trivial\n"+
					"         | clear H;elimAnd]\n"+
					"       end\n"+
					"  | [H: _ |- _ ] => genclear H;elimAnd\n"+
					"  | _ => intros; repeat match goal with [H: _ |- _ /\\ _] => split end\n"+
					"  end.\n");
	
	}
	
	
	/**
	 * uses: nothing
	 * provides: elimNor
	 * @param stream
	 */
	public void elimOr(PrintStream stream) {
		stream.println("(**\n" +
				" ** elimNor\n" +
				"This tactic is used to remove the not in front of a or (in the hypothesis),\n" +
				"turning [~ (A \\/  B) ] into [(~ A) /\\ (~ B)]. \n\n" +
				"*)\n");
		stream.println("Definition distr_or : forall A B, ~ (A \\/ B) ->  ~ A.\n" +
				   " intros A B a b.\n" +
				   " elim a; trivial.  left; trivial.\n" +
				   "Qed.\n");
		stream.println("Definition distr_or_inv : forall A B, ~ (A \\/ B) ->  ~B.\n" +
					   " intros A B a b.\n" +
					   " elim a; trivial.  right; trivial.\n" +
				   	   "Qed.\n");
		stream.println("Ltac elimNorCons a b := let H1 := fresh \"H\" in \n" +
					   "                                          assert (H1 : ~ (a)); cut (~(a \\/ b)) ; auto;\n"+
				       "                                          let H2 := fresh \"H\" in \n"+
				       "                                          assert (H2 : ~ (b)); cut (~(a \\/ b)); auto.\n");
		stream.println("Ltac elimNor :=\n" +
					   "  repeat match goal with\n" +
					   "  |   [H: ~ (?a \\/ ?b) |- _ ] => elimNorCons a b; clear H;  let H0 := fresh \"H\" in (let H1 := fresh \"H\" in  (intros H0 H1; clear H0 H1))\n" +
				   	   "end.\n");

		stream.println(
				"Ltac elim_or H HT R:=\n" +
				"	match HT with\n" +
				"	   | ?A \\/ R =>\n" +
				"	         let h := fresh \"H\" in assert(h : A \\/  R); [apply H; intros; auto | idtac]\n" +
				"	 | R\\/ ?B  =>\n" +
				"	         let h := fresh \"H\" in assert(h : R \\/  B); [apply H; intros; auto |idtac]\n" +
				"	   |  ?C -> ?D => elim_or H D R\n"+
				"	end.\n");

		stream.println(
				"Ltac solve_or R :=\n" +
				"	 match goal with\n" +
				"	  | [H : R \\/ ?B |-_ ] => destruct H; auto; try contradiction; intros\n" +
				"	  | [H : ?A \\/ R |- _ ] => destruct H;  auto; try contradiction; intros\n" +
				"	  | [H : ?HT|- _ ] => elim_or H HT R; genclear H;solve_or R\n" +
				"	  | [H: _ |- _ ] => genclear H; solve_or R\n" +
				"	  | _ => intros\n" +
				"	end.\n");
		if(PreferencePage.getCoqUseCustomTacs()) {
			stream.println("Ltac elim_or := elimor.\n");
		}
		else {
			stream.println("Ltac solveOr :=\n" +
					"	 match goal with\n" +
					"	  | [H : _|- ?R ] =>  solve_or R\n" +
					"	end.\n");
		
			stream.println("Ltac simplOr_rec h name tail :=\n"+
					"	match h with\n"+
					"	|    ?A \\/ ?B -> ?C  => assert(tail -> A -> C); [intros; apply name;trivial; left;trivial| idtac];\n"+
					"	                                                assert(tail -> B -> C); [intros; apply name; trivial; right;trivial| idtac]; clear name\n"+
					"	|    ?A -> ?B => simplOr_rec B name (tail -> A)\n" +
					"	end.\n");

			stream.println("Ltac simplOr_im h name :=\n" +
					"	match h with\n" +
					"	|    ?A \\/ ?B -> ?C  => assert(A -> C); [intros; apply name; left;trivial| idtac];\n" +
					"	                                                assert(B -> C); [intros; apply name; right;trivial| idtac]; clear name\n" +
					"	|    ?A -> ?B => simplOr_rec B name A\n"+
					"	end.\n");
		
			stream.println("Ltac simplOr := \n" +
					"	repeat match goal with\n" +
					"	|   [H: ?A |- _] =>simplOr_im A H\n" +
					"	end.\n");
			stream.println("Ltac elimOr := simplOr.\n");
		}

	}
	
	
	
	/**
	 * uses: nothing
	 * provides elimIF
	 * @param stream
	 */
	public void elimif(PrintStream stream) {
		stream.println("(**\n" +
		" ** overriding; elimIF\n" +
		"These tactics are more for internal use; eliminating overriding constructions\n" +
		"and the hypothesis using REFeq and Zeq.\n\n"+
		"*)\n");

		stream.println("Ltac elimREFeq x y :=\n"+
				  "let H1 := fresh \"H\" in\n"+
				  "let H2 := fresh \"H\" in\n"+
				  "let H3:= fresh \"H\" in\n"+
				 "(assert (H1 := REFeq_eq x y);\n"+
				  "assert (H2 := REFeq_false_not_eq x y);\n"+
				  "destruct (REFeq x y);\n"+
				  "[assert (H3  := H1 (refl_equal true));clear H1 H2; try (subst x)\n"+
				  "| assert (H3 := H2 (refl_equal false));clear H1 H2]).\n");

			stream.println("Ltac overriding := \n" +
					"	  match goal with\n" +
					"	  | [H : ?a <> ?c |- overridingCoupleRef ?T ?f ?a ?b ?c = ?f ?c] =>\n" +
					"	            apply  overridingCoupleRef_diff; apply H\n" +
					"	  | [H : ?a = ?c |- overridingCoupleRef ?T ?f ?a ?b ?c = ?b] =>\n" +
					"	            apply  overridingCoupleRef_eq; apply H\n" +
					"	  | [H : ?a <> ?c |- overridingCoupleZ ?T ?f ?a ?b ?c = ?f ?c] =>\n" +
					"	            apply  overridingCoupleZ_diff; apply H\n" +
					"	  | [H : ?a = ?c |- overridingCoupleZ ?T ?f ?a ?b ?c = ?b] =>\n" +
					"	            apply  overridingCoupleZ_eq; apply H\n" +
				"	  end.");

			stream.println("Ltac EQ_is_eq :=\n" +
				"  repeat match goal with\n" +
				"  | [H : REFeq ?x ?y = true |- _ ] =>\n" +
				"           let H1 := fresh \"H\" in \n" +
				"           (assert (H1 :=  REFeq_eq x y H);clear H)\n" +
				"  |  [H : REFeq ?x ?y = false |- _ ] =>\n" +
				"           let H1 := fresh \"H\" in \n" +
				"           (assert (H1 :=  REFeq_false_not_eq x y H); clear H)\n" +
				"  | [H : Zeq_bool ?x ?y = true |- _ ] =>\n" +
				"           let H1 := fresh \"H\" in \n" +
				"           (assert (H1 :=  Zeq_eq x y H);clear H)\n" +
				"  |  [H : Zeq_bool ?x ?y = false |- _ ] =>\n" +
				"           let H1 := fresh \"H\" in \n" +
				"           (assert (H1 :=  Zeq_false_not_eq x y H); clear H)\n" +
				       "   end.");
		    stream.println(
		    		" Ltac generalize_all x :=\n" + 
					"	match goal with\n" + 
					"   | [H : context [x] |- _ ] => generalize H;clear H; generalize_all x\n" + 
					"   | _ => idtac\n" + 
					"   end.\n" + 
					"\n" + 
					" Ltac gendestruct x :=\n" + 
					"   generalize_all x;\n" + 
					"   generalize (refl_equal x);\n" + 
					"   pattern x at -1;\n" + 
		    		"   case x.");
			stream.println(" Ltac elimIF :=\n" + 
			"   repeat match goal with\n" + 
			"   | [H : context  [REFeq ?x ?x] |- _ ] => rewrite (REFeq_refl x) in H\n" + 
			"   | [H1 : REFeq ?x ?y = false, H2 : context [if (REFeq ?x ?y) then _ else _] |- _]  => \n" + 
			"      rewrite H1 in H2\n" + 
			"   | [H1 : REFeq ?x ?y = true, H2 : context [if (REFeq ?x ?y) then _ else _]  |- _] => \n" + 
			"       rewrite H1 in H2\n" + 
			"   | [H : context  [Zeq_bool ?x ?x] |- _ ] => rewrite (Zeq_refl x) in H\n" + 
			"   | [H1 : Zeq_bool ?x ?y = false, H2 : context [if (Zeq_bool ?x ?y) then _ else _] |- _]  => \n" + 
			"      rewrite H1 in H2\n" + 
			"   | [H1 : Zeq_bool ?x ?y = true, H2 : context [if (Zeq_bool ?x ?y) then _ else _]  |- _] => \n" + 
			"       rewrite H1 in H2\n" + 
			"   | [H : context [if ?b then _ else _ ]|- _] => gendestruct b;intros\n" + 
			"   | [|- context [if ?b then _ else _]] => gendestruct b;intros\n" + 
			"    end;EQ_is_eq;subst.\n" + 
			" \n");
	}
	
	
	
	/**
	 * uses: nothing
	 * provides: solveRefElm, unfoldArrayTypeAx
	 * @param stream
	 */
	public void arrayTacs(PrintStream stream) {
		stream.println("(**\n" +
		" ** Array Things\n" +
		"Old Tactics used in the tactic arrtac.\n\n" +
		"*)\n");

		stream.println("Ltac unfoldRefArrAx array pos := let H:= fresh \"H\" in (assert(H := refelementsDom (refelements array pos)  array pos);\n" +
					   "                                                                 let H1 := fresh \"H\" in (assert (H1 : refelements array pos = null \\/  instances (refelements array pos));\n"+ 
					   "                                                                                     [apply H; trivial | clear H])).\n\n" +
					   "Ltac unfoldArrayTypeAx arr := match goal with\n" +
					   "[H: (subtypes (typeof ?arr) (array (class ?c) ?n)) |- _] =>\n" +
					   "                   let H1:= fresh \"H\" in (assert(H1 := ArrayTypeAx arr c n);\n" +
					   "                                              let H2 := fresh \"H\" in (assert (H2 := H1 H); clear H))\n" +
					   "end.\n\n" +
					   
					   "Ltac solveRefElm := match goal with\n" +
					   "| [h : _ |- instances (refelements ?array ?pos)] =>\n" +
					   "                              unfoldRefArrAx array pos\n" +
					   "end.\n");
	}
	
	
	/**
	 * @param stream
	 */
	public void cleanup(PrintStream stream) {
		stream.println("(**\n" + 
		" ** Cleansing\n" +
		"To clean up the mess (sometimes).\n\n" +
		"*)\n");

		stream.println("Ltac cleanUp :=\n"+
				"repeat match goal with\n" +
				"| [H1: ?a, H2: ?a |- _] => clear H2" +
				"| [H1: ?a = ?a |- _ ] => clear H1" +
				//"| [H1: ?a \\/ ?a |- _ ] => clear H1" +
				"| [H1: ?a < ?b, H2: ?a <= ?b |- _] => clear H2\n" +
				"end.\n");
	}

	
	public void absurd(PrintStream str) {
		str.println("(**\n" +
		" ** Absurd\n" +
		"When there is a contradiction absurdJack can often solve it. It is mainly used\n" +
		"through autoJack.\n\n"+
		" *)\n");

	    str.println("Ltac absurdJack := \n" +
				"  match goal with\n" +
				"  | [H : true = false |- _] => inversion H\n" +
				"  | [H : false = true |- _] => inversion H\n" +
				"  | [H : ?x <> ?x |- _ ] => elim H;trivial \n" +
				"  | [H1 : ?x <> ?y, H2 : ?x = ?y |- _] => elim (H1 H2)\n" +
				"  | [H: Zpos _ < 0 |- _] => discriminate H\n" +
				"  | [H: Zpos _ <= 0 |- _]=> elim H;trivial\n" +
				//"  | [H:~(_ <= _) |- _] => elim H;omega \n" +
				//"  | [H:~(_ < _) |- _] => elim H;omega \n" + 
				//"  | [H:~(_ >= _) |- _] => elim H;omega \n" +
				//"  | [H:~(_ > _) |- _] => elim H;omega \n" +
				"  | [H : subtypes _ _ |- _ ] => simpl in H; match type of H with False => elim H end\n" +
				"  | [H1 : arraylength ?x = _, H2 : context [j_sub (arraylength ?x) _] |- _] =>\n" +
				"        rewrite H1 in H2;simpl in H2;absurdJack\n" +
				"  | [H : ?x -> subtypes _ _ |- _ ] =>\n"+
			    "    simpl in H;\n" + 
			    "    match type of H with _ -> False => elim H; auto end\n" +
				"  | _ => try discriminate\n" +
			    "  end.");
			    str.println("Ltac absurdJackTougher := \n" +
						"  match goal with\n" +
	/*					"  | [H : ?x <> ?x |- _ ] => elim H;trivial \n" +
						"  | [H1 : ?x <> ?y, H2 : ?x = ?y |- _] => elim (H1 H2)\n" +
						"  | [H:~(_ <= _) |- _] => elim H;omega \n" +
						"  | [H:~(_ < _) |- _] => elim H;omega \n" + 
						"  | [H:~(_ >= _) |- _] => elim H;omega \n" +
						"  | [H:~(_ > _) |- _] => elim H;omega \n" +
						"  | [H: Zpos _ < Z0 |- _] => discriminate H\n" +
						"  | [H: Zpos _ <= Z0 |- _]=> elim H;trivial\n" +
						"  | [H : subtypes _ _ |- _ ] => simpl in H; match type of H with False => elim H end\n" +
						"  | [H1 : arraylength ?x = _, H2 : context [j_sub (arraylength ?x) _] |- _] =>\n" +
						"        rewrite H1 in H2;simpl in H2;absurdJack\n" + */
						"  | [H : ?x -> subtypes _ _ |- _ ] =>\n"+
					    "  simpl in H;\n" + 
					    " match type of H with _ -> False => elim H; auto end\n" +
						"  | _ => idtac\n" +
					    "  end.");
	}
	
	
	public void macros(PrintStream str) {
		str.println("(**\n" +
				" ** Some Macros\n" +
				" *** j_omega\n" +
				"it is used for arithmetic solving on java types.\n" +
				" *** solveOver\n" +
				"it is used to simplify overriding constructions.\n\n" +
				"*)\n");
		str.println("Ltac j_omega := try (unfold j_le, j_add, j_mul, j_lt, j_sub in *; omega).");
		str.println("Ltac solveOver := \n" +
				   "        unfold overridingCoupleZ, overridingCoupleRef in *; elimIF.\n" +
				   " \n");
	}
	
	public void automatic(PrintStream str) {
		str.println("(**\n" +
				 " ** Automatic proving\n"+
				 " *** autoJack\n"+
				 "Jack's CoqPlugin's auto tactic.\n"+
				 " *** tryApply\n"+
				 "To automatically solve a goal applying an hypothesis.\n"+
				 " *** startJack\n"+
				 "To prepare things up (doing some intros; unfolding several things).\n"+
				 " *** light and tough AutoJack\n" +
			"Used for automatic proving.\n\n"+
		"*)\n");

		str.println(
			"Ltac autoJack := \n" + 
			"   auto;\n" + 
			"   try overriding;\n" + 
			"   try absurdJack;\n" + 
			"   try (solveOver;auto;absurdJack).\n" + 
			"\n" + 
			"Ltac tryApply :=\n" + 
			"  match goal with \n" + 
			"  | [ H : _ |- _ ] => ((intros;apply H;autoJack) || (generalize H;clear H;tryApply))\n" + 
			"  | _ => intros\n" + 
			" end.\n" + 
			"\n" + 
			"Ltac intuiJack := cleanUp; elimOr; elimAnd; autoJack.\n" +
			"Ltac Folie := do 2 (elimIF; tryApply; autoJack; intuition; autoJack).\n" + 
			"\n" + 
			"Ltac lightStartJack := intros; unfold singleton, union, functionEquals, interval in *."+
			"\n" +
			"Ltac lightAutoJack := lightStartJack; autoJack; try j_omega.\n" +
			"\n" +
			"Ltac toughAutoJack := lightStartJack; Folie.\n" +
			"\n" +
			" Ltac startJack := lightStartJack; solveInc; cleanUp; intros.\n" + 
			"\n");
	}
	public void destrJle(PrintStream str) {
		str.println("(**\n" +
		" ** destrJle\n" +
		"Used to destruct loops: when you have [i <= b] and you want to have two cases:\n" +
		"[i < b] and [i = b].\n\n" +
		"*)\n");

		str.println(
				"Ltac destrJle n :=\n"+
		"    let H := fresh \"H\" in (assert (H: n); [j_omega | idtac]; destruct (j_le_lt_or_eq _ _ H); auto).\n");
	}
	
	/**
	 * 
	 * @author jcharles
	 *
	 */
	public void arrtac(PrintStream str) {
		str.println("(**\n" +
		" ** Some more array tactics\n" +
		" *** arrlen\n"+
		" To use when you have things to prove on the length of arrays.\n"+
		" *** arrtype\n"+
		" To use when you have things to prove on the subtypes of arrays.\n"+
		" *** arrelm\n"+
		" To use when a goal has the form [instance (refelements arr i)].\n"+
		" *** arrtac\n"+
		" An auto tactic for arrays using all of the above.\n\n"+
		"*)\n");

		str.println(
		"Ltac arrlen :=\n" +
	    "   eapply arraylenAx; eauto.\n" + 
		"Ltac arrtype := eapply ArrayTypeAx; eauto.\n" +
		"Ltac arrelm := solveRefElm; autoJack.\n");
		str.println(
		"Ltac find_subtype_array t T :=\n" + 
		"    match T with\n" +
		"    | subtypes (typeof t) (array _ _) => constr:T\n"+
		"    | ?A -> ?B => find_subtype_array t B\n"+
		"    end.\n");
		str.println(
		"Ltac assertsubtypes_array t :=\n"+
		"    match goal with\n" +
		"    | [H: ?T |- _] => \n" +
		"      match find_subtype_array t T with\n" +
		"      |  ?res => assert (res); [apply H | intros;arrlen]\n" +
		"      end\n"+
		"    end.\n");
		str.println(
		"Ltac le_arraylength :=\n" +
		"  match goal with\n" +
		"  | [|- 0 <= arraylength ?t] =>\n"+
		"     assertsubtypes_array t\n" +
		"  end.\n");
		str.println("Ltac array_tac :=\n" +
		"  match goal with\n" +
		"  | [|- instances (refelements _ _)] => arrelm\n" +
		"  | [|- subtypes (typeof (refelements _ _)) _] => arrtype\n" +
		"  | [|- 0 <=  arraylength ?t] =>\n" +
		"     assertsubtypes_array t; try array_tac\n" +
		"  | _ => idtac\n" +
		"  end.\n");
		str.println("Ltac arrtac := array_tac.\n");
	}
	
	public void purity(PrintStream ps) {
		ps.println( "Ltac simpl_pure :=\n" +
					"	repeat match goal with\n" +
					"	| [H:  (forall (_ : _) (_ : _),  (_ = _) -> (_ = _) -> _) |- _] =>\n" + 
					"	          (let h := fresh \"H\" in  (assert(h := \n" +
					"	                   (H _ _ (refl_equal _) (refl_equal _))); clear H; assert(H := h); clear h))\n" +
					"\n" +
					"	| [H:  (forall (_ : _),  (_ = _) -> _) |- _] => \n" +
					"	          (let h := fresh \"H\" in  (assert(h := \n" +
					"	                   (H _ (refl_equal _))); clear H; assert(H := h); clear h))\n" +
					"	end;\n" +
					"	intros.\n");
	}
	 public void pattern_right(PrintStream p) {
		 p.println("(* match2fun courtesy of J.Forest *)");
		 p.println("Ltac match2fun exp pat :=\n" +
					"  let exp' := eval pattern pat in exp in\n" +
					"  let f := match exp' with\n" +
					"           |(?h _) => constr:h\n" +
					"           end\n" +
					"  in constr:f.");
		 
		 p.println("Ltac refl_goal := match goal with\n" +
					"|  [_: _ |- eq (?a ?i) ?b ] =>\n"+ 
					"	let f := match2fun b i in\n" +
					"	change b with (f i)\n" +
					"end; reflexivity.\n");
		 p.println("Ltac extac_intern := intros;\n" +
				 "   match goal with\n" +
				 "   | [ _ : _ |- _ /\\ _ ] => apply conj; [idtac |extac_intern]\n" +
				 "   | _ => intros; subst; refl_goal\n" +
				 "   end.\n" +
				 "Ltac extac := eapply ex_intro; extac_intern.\n");
		 
	 }
	 
	 public void rewrite_all(PrintStream p) {
		 p.println("(* found on http://cocorico.cs.ru.nl *)\n" +
				 " Ltac rewrite_all H :=\n" + 
				 "	 match type of H with\n" +
				 "	 | ?t1 = ?t2 => \n" +
				 "	   let rec aux H :=\n" +
				 "	     match goal with\n" +
				 "	     | id : context [t1] |- _ =>\n" + 
				 "	       match type of id with \n" +
				 "	       | t1 = t2 => fail 1 \n" + 
				 "	       | _ => generalize id;clear id; try aux H; intro id\n" +
				 "	       end\n" +
				 "	     | _ => try rewrite H\n" +
				 "	     end in\n" +
				 "	   aux H\n" +
		 		"	 end.");


	 }
}

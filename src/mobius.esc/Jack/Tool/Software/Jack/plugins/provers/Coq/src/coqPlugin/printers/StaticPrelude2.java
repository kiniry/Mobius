/*
 * Created on Feb 23, 2005
 */
package coqPlugin.printers;

import java.io.File;
import java.io.PrintStream;

import coqPlugin.language.CoqType;

import jml2b.IJml2bConfiguration;

/**
 * @author jcharles
 *
 */
public class StaticPrelude2 extends Printer {
	/** the file containing the module: jack_references */
	public static final String fileName = "jack_references";
	
	/** the module contained in the file: JackReferences */
	public static final String moduleName = "JackReferences";
	
	private String outDir;
	
	public StaticPrelude2(File output_directory, IJml2bConfiguration config) {
		super(output_directory, fileName + ".v");		
		outDir = output_directory.getAbsolutePath() + File.separator;
		startWriting(config);
	}
	protected void writeToFile(PrintStream stream, IJml2bConfiguration config){
		stream.println("Require Import ZArith.");
		stream.println("Require Import \"" + outDir + StaticPrelude1.fileName + "\".");
		stream.println("Import " + StaticPrelude1.moduleName + ".\n");
		
		stream.println("Module Type JackClasses.");
		stream.println("  Parameter Classes: Set.");
		stream.println("  Parameter StringClass : Classes.");
		stream.println("  Parameter IntClass : Classes.");
		stream.println("  Parameter ShortClass : Classes.");
		stream.println("  Parameter CharClass : Classes.");
		stream.println("  Parameter ByteClass : Classes.");
		stream.println("  Parameter BooleanClass : Classes.");
		stream.println("End JackClasses.\n");

		stream.println("Variable "+ CoqType.Reference +" : Set.");
		stream.println("Variable null : "+ CoqType.Reference +".");
		stream.println("Module JackReferences (Arg: JackClasses).");
		stream.println("Definition Classes := Arg.Classes.");
		stream.println("Definition StringClass := Arg.StringClass.");
		stream.println("Definition IntClass := Arg.IntClass.");
		stream.println("Definition ShortClass := Arg.ShortClass.");
		stream.println("Definition CharClass := Arg.CharClass.");
		stream.println("Definition ByteClass := Arg.ByteClass.");
		stream.println("Definition BooleanClass := Arg.BooleanClass.");

		defineObjects(stream);
		stream.println();
		defineArrays(stream);
		stream.println("End JackReferences.");
	}
	
	/**
	 * Prints the memory model variable definitions
	 **/
	private void defineObjects(PrintStream stream) {
		
		stream.println("");
		stream.println("(* Objects Definitions *)");
		stream.println("Inductive Types : Set :=");
		stream.println("    class : Classes -> Types ");
		stream.println("|   array : Types -> Z -> Types.\n");
		stream.println("");
		
		stream.println("Variable instanceof : "+ CoqType.Reference +" -> Types -> Prop.\n");

		stream.println("");
		stream.println("Variable STRING : Set.");
		stream.println("Variable j_string : STRING -> "+ CoqType.Reference +".");

		stream.println("Variable instances : "+ CoqType.Reference +" -> Prop.");
		stream.println("Axiom nullInstances : (not (instances null)).\n");
		stream.println("");
		stream.println("Variable typeof : "+ CoqType.Reference +" -> Types.");
		printMyBoolEq(stream);
		//stream.println(
		//	"Axiom typeofDom :"
		//		+ "(r:"+ CoqType.Reference +") (instances r) <->(dom "+ CoqType.Reference +" Types typeof r).");
		//		stream.println(
		//			"Definition typeofOver : "
		//				+ "("+ CoqType.Reference +" -> Types) -> "
		//				+ ""+ CoqType.Reference +" -> Types -> "+ CoqType.Reference +" -> Types");
		//		stream.println(
		//			"   := [f:"+ CoqType.Reference +" -> Types][a:"+ CoqType.Reference +"]"
		//				+ "[b:Types][a1:"+ CoqType.Reference +"]");
		//		stream.println("      if (REFeq "+ CoqType.Reference +" a a1)");
		//		stream.println("      then b ");
		//		stream.println("      else (f a1).\n");
		//
		stream.println("Definition singleton (a:Set) (r s:a) := r = s :> a.");
		stream.println(
			"Definition union (s:Set) (a b:s -> Prop) (c:s) := (a c) \\/ (b c).");
		stream.println(
			"Definition equalsOnOldInstances (s:Set) (f g:"+ CoqType.Reference +" -> s) :="
				+ "forall x:"+ CoqType.Reference +", (instances x) -> (f x) = (g x) :> s.");
		stream.println(
			"Definition intersectionIsNotEmpty (s:Set)(f g:s->Prop) :="
				+ " (exists y : _, (f y) /\\ (g y)).");
		stream.println("");
		stream.println(
			"Definition  overridingCoupleRef (T:Set) (f:"+ CoqType.Reference +" -> T)(a:"+ CoqType.Reference +") (b:T) (c:"+ CoqType.Reference +") :="
				+ " if (REFeq a c) then b else (f c).");
		stream.println("Lemma overridingCoupleRef_diff : forall T f a b c, a <> c -> overridingCoupleRef T f a b c = f c.\n" + 
				"Proof. intros; unfold overridingCoupleRef; rewrite not_eq_false_REFeq; trivial. Qed.");

		stream.println("Lemma overridingCoupleRef_eq : forall T f a b c, a = c -> overridingCoupleRef T f a b c = b.\n" +
				"Proof. intros; unfold overridingCoupleRef; rewrite REFeq_eq_true; trivial. Qed.");
		stream.println(
				"Definition  overridingCoupleZ (T:Set) (f:Z -> T)(a:Z) (b:T) (c:Z) :="
					+ " if (Zeq_bool a c) then b else (f c).");
		stream.println("Lemma overridingCoupleZ_diff : forall T f a b c, a <> c -> overridingCoupleZ T f a b c = f c.\n" + 
		"Proof. intros; unfold overridingCoupleZ; rewrite not_eq_false_Zeq; trivial. Qed.");

	//	stream.println("Lemma overridingCoupleZ_eq : forall T f a b c, a = c -> overridingCoupleRef T f a b c = b.\n" +
	//	"Proof. " +
	//	" intros T f a b c H; unfold overridingCoupleZ,Zeq; rewrite H; " +
	//	" rewrite Zcompare_refl; trivial. " +
	//	"Qed.");
		stream.println("Lemma overridingCoupleZ_eq : forall T f a b c, a = c -> overridingCoupleZ T f a b c = b. " +
				"\nProof." +
				"\n intros T f a b c H; unfold overridingCoupleZ; rewrite (Zeq_eq_true _ _ H); trivial." +
				"\nQed.");




		stream.println("");

//		stream.println(
//			"Variable overridingArray : forall s t u:Set, (s->t->u)->(s->Prop)->(t->Prop)->u->s->t->u.");
		stream.println("Definition overridingArray (Ref :Set) (tind : Set) (tret : Set)\n" +  
						"	(elems: Ref -> tind -> tret) \n" +
						"	(testRef: Ref -> bool)\n" +
						"	(testRange: tind -> bool)\n" +
						"	(res : tret) \n" +
						"	(arg1 : Ref)\n" +
						"	(arg2 : tind) := \n" +
						"		if (testRef arg1) then \n" +
						"			if(testRange arg2) then \n" +
						"				res\n" +
						"			else\n" +
						"				elems arg1 arg2\n" +
						"		else\n" +
						"			elems arg1 arg2.\n");
		
//		
//		stream.println(
//			"Axiom overridingArray_t_t : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), "
//				+ "(a x) -> (b y) -> ((overridingArray s t u f a b c x y) = c :> u).");
//
//		stream.println(
//			"Axiom overridingArray_t_f : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), "
//				+ "(a x) -> ~(b y) -> ((overridingArray s t u f a b c x y) = (f x y) :> u).");
//
//		stream.println(
//			"Axiom overridingArray_f : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), "
//				+ "~(a x) -> ((overridingArray s t u f a b c x y) = (f x y) :> u).");

		stream.println(
			"Definition setEquals (s: Set) (f g: s->Prop) :="
				+ " forall x: s, (f x) -> (g x) /\\ (g x) -> (f x).");
		stream.println(
			"Definition functionEquals (s t: Set)(f g: s->t) := "
				+ "forall x: s, ((f x) = (g x) :> t).");
		stream.println(
			"Definition interval (a b: Z) (c: Z) := (j_le a c) /\\ (j_le c b).");
//		stream.println("Variable boolf : Prop -> bool.");
//		stream.println(
//			"Axiom boolf_t : (a : Prop) a -> (eq bool (boolf a) true).");
//		stream.println(
//			"Axiom boolf_f : (a : Prop) ~a -> (eq bool (boolf a) false).");

		stream.println("Variable question : forall t: Type, Prop -> t -> t -> t.");
		stream.println(
			"Axiom question_t : forall (t: Set) (x: Prop) (y z: t), x -> ((question t x y z) = y :> t).");
		stream.println(
			"Axiom question_f : forall (t: Set) (x: Prop) (y z: t), ~x -> ((question t x y z) = z :> t).\n");
		
		stream.println("Definition j_stringRan : STRING -> Prop ");
		stream.println(
				"   := fun (s:STRING) =>(instanceof (j_string s) (class StringClass)).\n");


	}


	
	/**
	 * 
	 */

	private void printMyBoolEq(PrintStream stream) {
		stream.println("Lemma not_true_is_false: forall (b: bool), ~(b=true) -> b=false.");
		stream.println("Proof.\n" +
				"induction b. intro; elim H; auto. intro; auto.\n" +
				"Qed.\n");
		
		stream.println("Variable REFeq : "+ CoqType.Reference +" -> "+ CoqType.Reference +" -> bool.");
		stream.println("Variable REFeq_refl : forall x, REFeq x x = true. ");
		stream.println(
			"Variable REFeq_eq : forall x y, REFeq x y = true -> x = y. ");
		stream.println(
			"Lemma REFeq_eq_true : forall x y, x = y-> REFeq x y = true.");
		stream.println("Proof.");
		stream.println("intros x y H. rewrite H. apply REFeq_refl.");
		stream.println("Qed. ");
		stream.println(
			"Lemma REFeq_eq_not_false : forall x y, x=y-> REFeq x y <> false.");
		stream.println("Proof.");
		stream.println("intros x y e. rewrite REFeq_eq_true; trivial; discriminate.");
		stream.println("Qed. ");
		stream.println(
			"Lemma REFeq_false_not_eq :  forall x y, REFeq x y = false -> x <> y.");
		stream.println("Proof.");
		stream.println(
			"exact (fun x y H e => REFeq_eq_not_false x y e H).");
		stream.println("Qed. ");
		stream.println(
			"Definition exists_REFeq_eq : forall x y, {b:bool  | REFeq x y = b}.");
		stream.println("Proof.");
		stream.println(" intros. exists (REFeq x y). constructor.");
		stream.println("Qed. ");
		stream.println(
			"Lemma not_eq_false_REFeq : forall x y, x <> y -> REFeq x y = false.");
		stream.println("Proof.");
		stream.println(" intros x y H. apply not_true_is_false.");
		stream.println(" intro. apply H. apply REFeq_eq. assumption.");
		stream.println("Qed. ");
		stream.println("Lemma eq_dec : forall (x y:"+ CoqType.Reference +"), {x = y} + {x <> y}.");
		stream.println("Proof.");
		stream.println(" intros x y; case (exists_REFeq_eq x y). intros b; case b; intro H.");
		stream.println(" left; apply REFeq_eq; assumption. right; apply REFeq_false_not_eq ; assumption.");
		stream.println("Qed.");
		stream.println("Lemma Zeq_refl : forall x, Zeq_bool x x = true.\n" +
				"Proof.\n" +
				" intros; unfold Zeq_bool; rewrite Zcompare_refl; trivial.\n" +
				"Qed.");
		stream.println(
			"Lemma Zeq_eq : forall x y, Zeq_bool x y = true -> x = y.\n" +
			" intros x y H.\n" + 
			"unfold Zeq_bool in *.\n" +
			"destruct ( Zcompare_Eq_iff_eq x y) as [h1 h2].\n" +
			"apply h1.\n" +
			"destruct (x ?= y); try discriminate; auto.\n" +
			"Qed.");
		 
		stream.println("Lemma Zeq_eq_true: forall x y, x = y -> Zeq_bool x y = true.\n" +
				"Proof.\n" +
				" intros x y H;rewrite H;apply Zeq_refl.\n" +
				"Qed.");
			

		stream.println("Lemma not_eq_false_Zeq : forall x y, x<>y -> Zeq_bool x y = false.\n" +
				"Proof.\n" +
				" intros x y H.\n" +
				"destruct ( Zcompare_Eq_iff_eq x y) as [h1 h2]. unfold Zeq_bool.\n" +
				"destruct (x ?= y); auto.\n" +
				"destruct H; auto.\n" +
				"Qed.");
		
		stream.println("Lemma Zeq_false_not_eq :  forall x y, Zeq_bool x y = false -> x <> y.\n" +
				"Proof.\n" +
				" intros x y H1 H2; rewrite H2 in H1; rewrite Zeq_refl in H1; discriminate H1.\n" +
				"Qed. ");
	}
	public boolean mustRewrite() {
		return true;
	}
	
	
	
	private void defineArray(PrintStream stream, String t, String cname) {
		
		stream.println("Variable " + t + "elements : "+ CoqType.Reference +" -> t_int -> t_"+ t+".");
		stream.println(
			"Definition "
				+ t
				+ "elementsDomDef (r:"+ CoqType.Reference +"): Prop :="
				+ " (instances r) "
				+ "/\\ ((typeof r) = (array (class "
				+ cname
				+ ") 1) :> Types).");
/*		stream.println("Axiom " + t + "elementsDom : ");
		stream.println(
			"   forall r:"+ CoqType.Reference +", ((instances r) "
				+ "/\\ (eq Types (typeof r) (array c_"
				+ t
				+ " `1`)))"
				+ " <-> (dom "+ CoqType.Reference +" Z->Z "
				+ t
				+ "elements r).");
		stream.println(
			"Definition "
				+ t
				+ "elementsDomDomDef : "+ CoqType.Reference +" -> Z -> Prop :=");
		stream.println("   [r:"+ CoqType.Reference +"][z:Z] (" + t + "elementsDomDef r)");
		stream.println("/\\ (Zle `0` z) /\\ (Zlt z (arraylength r)).");
		stream.println("Axiom " + t + "elementsDomDom : ");
		stream.println(
			"   (r:"+ CoqType.Reference +")(z:Z) ("
				+ t
				+ "elementsDomDomDef r z)"
				+ " <-> (dom Z Z ("
				+ t
				+ "elements r) z).");
		stream.println("Axiom " + t + "elementsRan : ");
		stream.println(
			"   (r:"+ CoqType.Reference +")(z:Z) "
				+ "("
				+ t
				+ "elementsDomDef r) -> "
				+ "("
				+ t
				+ "elementsDomDomDef r z) -> "
				+ "(t_"
				+ t
				+ " ("
				+ t
				+ "elements r z)).\n");*/
	}

	/**
	 * Prints the variables corresponding to arrays.
	 **/
	private void defineArrays(PrintStream stream) {
		stream.println("\n");
		stream.println("(* Time to play with the arrays. *)");
		stream.println("Variable elemtype : Types -> Types.");
		stream.println("Definition elemtypeDomDef (t:Types): Prop :=");
		stream.println("    match t with");
		stream.println("    |    (class _) => False ");
		stream.println("    |    (array cl n) => (1 <= n)");
		stream.println("    end.");
//		stream.println(
//			"Axiom elemtypeDom : "
//				+ "(t:Types) (elemtypeDomDef t) <-> (dom Types Types elemtype t).");
		stream.println(
			"Axiom elemtypeAx : forall (c : Types) (n : Z), (1 <= n) -> ");
		stream.println(
			"   ((elemtype (array c n)) = (array c (n - 1))).\n");

		stream.println("Variable arraylength : "+ CoqType.Reference +" -> t_int.");
//		stream.println("Axiom arraylengthDom : ");
//		stream.println(
//			"   (r:"+ CoqType.Reference +") (elemtypeDomDef (typeof r)) <-> (dom "+ CoqType.Reference +" Z arraylength r).\n");
		defineArray(stream, "int", "IntClass");
		defineArray(stream, "short", "ShortClass");
		defineArray(stream, "char", "CharClass");
		defineArray(stream, "byte", "ByteClass");

		stream.println("Variable booleanelements : "+ CoqType.Reference +" -> Z -> bool.");
		stream.println(
			"Axiom boolelementsDomDef : forall (r:"+ CoqType.Reference +"), "
				+ "(instances r) "
				+ "/\\ ((typeof r) = (array (class BooleanClass) 1)).");
	/*	stream.println("Axiom boolelementsDom : ");
		stream.println(
			"   (r:"+ CoqType.Reference +") ((instances r) "
				+ "/\\ ((typeof r) = (array c_boolean 1) :> Types))"
				+ " <-> (dom "+ CoqType.Reference +" Z->bool booleanelements r).");
		stream.println(
			"Definition boolelementsDomDomDef : "+ CoqType.Reference +" -> Z -> Prop :=");
		stream.println("   [r:"+ CoqType.Reference +"][z:Z] (boolelementsDomDef r)");
		stream.println("/\\ (Zle `0` z) /\\ (Zlt z (arraylength r)).");
		stream.println("Axiom boolelementsDomDom : ");
		stream.println(
			"   (r:"+ CoqType.Reference +")(z:Z) (boolelementsDomDomDef r z)"
				+ " <-> (dom Z bool (booleanelements r) z).");
*/
		stream.println("Variable refelements : "+ CoqType.Reference +" -> Z -> "+ CoqType.Reference +".");
		stream.println("Axiom refelementsDom : forall r a b, r = refelements a b -> (r = null \\/ instances r)."); 
		//stream.println(
		//		"Axiom refelementsDomDef : forall (r:"+ CoqType.Reference +"), "
		//			+ "(instances r) "
		//			+ "\\/ (r = null) .");
/*		stream.println("Axiom refelementsDom : ");
		stream.println("   (r:"+ CoqType.Reference +") ((instances r) ");
		stream.println("                    /\\ (elemtypeDomDef (typeof r))");
		stream.println(
			"                  /\\ ~(eq Types (typeof r) (array c_int `1`))");
		stream.println(
			"                  /\\ ~(eq Types (typeof r) (array c_short `1`))");
		stream.println(
			"                  /\\ ~(eq Types (typeof r) (array c_byte `1`))");
		//		stream.println(
		//			"                  /\\ ~(eq Types (typeof r) (array c_long `1`))");
		stream.println(
			"                  /\\ ~(eq Types (typeof r) (array c_char `1`)))"
				+ " <-> (dom "+ CoqType.Reference +" Z -> "+ CoqType.Reference +" refelements r).");*/
	}
}

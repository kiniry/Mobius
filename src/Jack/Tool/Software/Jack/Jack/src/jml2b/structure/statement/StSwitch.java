//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StSwitch.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.io.Serializable;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.util.ModifiableSet;
import jml2b.util.Profiler;
import antlr.collections.AST;

/**
 * This class describes a list of cases.
 * @author L. Burdy, A. Requet
 **/
class CasesList extends Profiler implements Serializable, IFormToken {

	/**
	 * Returns the sequence corresponding to the default statement sequenced 
	 * with the statement of a cases list corresponding to the cases that are
	 * defined after the default clause.
	 * @param defaul The default statement
	 * @param cases The cases list
	 * @return The explicit sequence corresponding to the default case.
	 **/
	/*@
	  @ ensures \result != null;
	  @*/
	static Statement sequence(Statement defaul, CasesList cases) {
		if (cases == null)
			return defaul;
		StSequence s = new StSequence(cases.body, defaul, cases.body);
		if (cases.next == null) {
			return s;
		} else
			return sequence(s, cases.next);
	}

	/**
	 * The expression corresponding to the current case
	 **/
	private Expression exp;

	/**
	 * The body of the current case
	 **/
	private Statement body;

	/**
	 * The next element of the list
	 **/
	private CasesList next;

	/*@
	  @ ghost boolean parsed = false;
	  @ invariant parsed ==> exp != null
	  @        && parsed ==> body != null
	  @        && parsed ==> exp.parsed
	  @        && parsed ==> body.parsed
	  @        && parsed && next != null ==> next.parsed;
	  @*/

	String emit() {
		String s = "case " + exp.toJava(0) + " : " + body.emit();
		if (next != null)
			s += next.emit();
		return s;
	}

	/*@
	  @ requires parsed;
	  @*/
	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		body.linkStatement(config, f);
		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	public void typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		body.typeCheck(config, f);
		if (next != null)
			next.typeCheck(config, f);
	}

	/**
	 * Collects all the indentifier of the list to give them an index in 
	 * the identifer array. This array is then analyzed to give short name when 
	 * it is possible to identifiers.
	 * Instancie the statement of the list.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @param definingClass The class where this statement is defined
	 * @return the normalized list
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	/*@
	  @ requires parsed;
	  @*/
	CasesList jmlNormalize(IJml2bConfiguration config, Class definingClass)
		throws PogException {
		exp = (Expression) exp.jmlNormalize(config, definingClass);
		body = (Statement) body.jmlNormalize(config, definingClass);
		if (next != null)
			next = next.jmlNormalize(config, definingClass);
		return this;
	}

	/**
	 * Returns the sequence corresponding to the current case sequenced with the
	 * next elements of the list, the default statement and another list of 
	 * cases.
	 * @param defaul The default statement
	 * @param cases The cases list
	 * @return the explicit sequence corresponding to the current case.
	 **/
	/*@
	  @ requires parsed;
	  @*/
	private Statement sequences(Statement defaul, CasesList cases2) {
		Statement s = sequence(body, next);
		if (s == null)
			return sequence(defaul, cases2);
		Statement t = new StSequence(s, s, defaul);
		return sequence(t, cases2);
	}

	/**
	 * Returns the proofs resulting where the WP calculus apply on this 
	 * list of cases considered as the list of cases that are declared before
	 * the default clause.
	 * @param config The current configuration
	 * @param vv The temporary variable corresponding to the expression
	 * tested in the switch
	 * @param switchDefault The default statement
	 * @param switchCase2 The list of cases that are declared after the 
	 * default.
	 * @param normalBehaviour theorems to ensure if the statement terminates
	 * normally
	 * @param finishOnReturn theorems to ensure if the statement terminates
	 * abruptly on a <code>return</code>
	 * @param finishOnBreakLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>break</code>
	 * @param finishOnContinueLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>continue</code>
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * statement terminates abruply on an exception
	 * @return the proofs obligation resulting from the WP calculus
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	Proofs switchBeforeDefault(
		IJml2bConfiguration config,
		String vv,
		Statement switchDefault,
		CasesList switchCase2,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {

		FormulaWithSpecMethodDecl fwp = exp.exprToForm(config);
		FormulaWithSpecMethodDecl s =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				fwp.getFormula()));

		Proofs w =
			sequences(switchDefault, switchCase2).wp(
				config,
				normalBehaviour,
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);

		w.addHyp(s, new ColoredInfo(exp), VirtualFormula.LOCALES);
		if (next != null)
			w.addAll(
				next.switchBeforeDefault(
					config,
					vv,
					switchDefault,
					switchCase2,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));
		return w;
	}

	/**
	 * Returns the proofs resulting where the WP calculus apply on this 
	 * list of cases considered as the list of cases that are declared after
	 * the default clause.
	 * @param config The current configuration
	 * @param vv The temporary variable corresponding to the expression
	 * tested in the switch
	 * @param normalBehaviour theorems to ensure if the statement terminates
	 * normally
	 * @param finishOnReturn theorems to ensure if the statement terminates
	 * abruptly on a <code>return</code>
	 * @param finishOnBreakLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>break</code>
	 * @param finishOnContinueLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>continue</code>
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * statement terminates abruply on an exception
	 * @return the proofs obligation resulting from the WP calculus
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	Proofs switchAfterDefault(
		IJml2bConfiguration config,
		String vv,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		FormulaWithSpecMethodDecl fwp = exp.exprToForm(config);
		FormulaWithSpecMethodDecl s =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				fwp.getFormula()));

		Proofs w =
			sequence(body, next).wp(
				config,
				normalBehaviour,
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);

		w.addHyp(s, new ColoredInfo(exp), VirtualFormula.LOCALES);

		if (next != null)
			w.addAll(
				next.switchAfterDefault(
					config,
					vv,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));
		return w;
	}

	/**
	 * Returns the body.
	 * @return <code>body</code>
	 */
	Statement getBody() {
		return body;
	}

	/**
	 * Returns the expression corresponding to the current case.
	 * @return <code>exp</code>
	 */
	Expression getExp() {
		return exp;
	}

	/**
	 * Returns the next element of the list.
	 * @return <code>next</code>
	 */
	CasesList getNext() {
		return next;
	}

	/**
	 * Sets the body.
	 * @param body The body to set
	 */
	void setBody(Statement body) {
		this.body = body;
	}

	/**
	 * Sets the exp.
	 * @param exp The exp to set
	 */
	void setExp(Expression exp) {
		this.exp = exp;
	}

	/**
	 * Sets the next.
	 * @param next The next to set
	 */
	void setNext(CasesList next) {
		this.next = next;
	}

	static final long serialVersionUID = -628097474613912972L;

}

/**
 * This class implements a switch statement
 * @author L. Burdy
 **/
public class StSwitch extends Statement {

	/**
	 * Returns the default condition constructed from a list of cases.
	 * @param config The current configuration
	 * @param vv The value to compared
	 * @param cases1 The list of cases
	 * @return the disjonction of all the cases expression equality with vv.
	 **/
	private static FormulaWithSpecMethodDecl switchDefault(
		IJml2bConfiguration config,
		String vv,
		CasesList cases1)
		throws Jml2bException, PogException {
		FormulaWithSpecMethodDecl tmp;
		if (cases1 == null)
			return null;
		FormulaWithSpecMethodDecl fwp = cases1.getExp().exprToForm(config);
		FormulaWithSpecMethodDecl s =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				fwp.getFormula()));
		if ((tmp = switchDefault(config, vv, cases1.getNext())) == null)
			return s;
		else
			return FormulaWithSpecMethodDecl.or(s, tmp);
	}

	/**
	 * Returns the default condition constructed from all the cases negation.
	 * @param config The current configuration
	 * @param vv value to compared
	 * @param cases1 list of cases
	 * @param cases2 list of cases
	 * @return the disjonction of all the cases expression equality with vv.
	 **/
	private static FormulaWithSpecMethodDecl switchDefault(
		IJml2bConfiguration config,
		String vv,
		CasesList cases1,
		CasesList cases2)
		throws Jml2bException, PogException {
		FormulaWithSpecMethodDecl tmp;
		if (cases1 == null)
			return switchDefault(config, vv, cases2);
		FormulaWithSpecMethodDecl fwp =cases1.getExp().exprToForm(config);
		FormulaWithSpecMethodDecl s =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				fwp.getFormula()));
		if ((tmp = switchDefault(config, vv, cases1.getNext(), cases2))
			== null)
			return s;
		else
			return FormulaWithSpecMethodDecl.or(s, tmp);
	}

	/**
	 * The tested expression
	 **/
	private Expression exp;

	/**
	 * The default statement. It can not be <code>null</code>. If no default
	 * statement is declared, the statement is intialized with 
	 * <code>skip</code>.
	 **/
	private Statement switchDefault;

	/**
	 * The list of cases that appear before the default statement. This list is
	 * possibly <code>null</code>.
	 **/
	private CasesList switchCase1;

	/**
	 * The list of cases that appear after the default statement. This list is
	 * possibly <code>null</code>.
	 **/
	private CasesList switchCase2;

	/*@
	  @ invariant parsed ==> exp != null
	  @        && parsed ==> switchDefault != null
	  @        && parsed ==> exp.parsed
	  @        && parsed ==> switchDefault.parsed
	  @        && parsed && switchCase1 != null ==> switchCase1.parsed
	  @        && parsed && switchCase2 != null ==> switchCase2.parsed;
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StSwitch(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		String s = "switch (" + exp.toJava(0) + ") {\n";
		if (switchCase1 != null)
			s += switchCase1.emit();
		s += "default : " + switchDefault.emit();
		if (switchCase2 != null)
			s += switchCase2.emit();
		s += "}\n";
		return s;
	}

	/*@
	  @ modifies exp, switchCase1, switchCase2, switchDefault;
	  @ ensures exp != null && switchDefault != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {

		AST subtree = tree.getFirstChild();

		// Parses the tested expression
		exp = Expression.createE(getJmlFile(), subtree);
		subtree = exp.parse(subtree);

		// beforeDefault allows the store the parsed cases in switchCase1 or
		// switchCase2 depending on the fact that the default clause has already 
		// been parsed or not.
		boolean beforeDefault = true;
		CasesList t;

		while (subtree != null && subtree.getType() == CASE) {
			AST subsubtree = subtree.getFirstChild();
			while (subsubtree != null) {
				if (subsubtree.getType() == LITERAL_case) {
					CasesList s = new CasesList();

					// Parses the expression corresponding to the current
					// case.
					Expression e =
						Expression.createE(
							getJmlFile(),
							subsubtree.getNextSibling());
					subsubtree = e.parse(subsubtree.getNextSibling());
					s.setExp(e);

					// If the case does not have a body, a default body
					// corresponding to skip is assigned to the case
					if (subsubtree == null
						|| subsubtree.getType() == LITERAL_case
						|| subsubtree.getType() == LITERAL_default)
						s.setBody(new StSkip());
					else {
						// Parses the body of the case.
						while (subsubtree != null) {
							Statement s1 =
								Statement.createS(getJmlFile(), subsubtree);
							subsubtree = s1.parse(subsubtree);
							if (s.getBody() == null)
								s.setBody(s1);
							else
								s.setBody(
									new StSequence(this, s.getBody(), s1));
						}
					}
					//@ set s.parsed = true;
					// Stores the parsed cases at the end of the appropriate
					// list.
					if (beforeDefault)
						if (switchCase1 == null) {
							switchCase1 = s;
							continue;
						} else
							t = switchCase1;
					else if (switchCase2 == null) {
						switchCase2 = s;
						continue;
					} else
						t = switchCase2;
					while (t.getNext() != null)
						t = t.getNext();
					t.setNext(s);

				} else if (subsubtree.getType() == LITERAL_default) {
					// Parses the default case.
					beforeDefault = false;
					subsubtree = subsubtree.getNextSibling();

					// If the case does not have a body, a default body
					// corresponding to skip is assigned to the case
					if (subsubtree == null
						|| subsubtree.getType() == LITERAL_case) {
						switchDefault = new StSkip();
					} else {
						// Parses the body of the default case.
						while (subsubtree != null) {
							Statement s1 =
								Statement.createS(getJmlFile(), subsubtree);
							subsubtree = s1.parse(subsubtree);
							if (switchDefault == null)
								switchDefault = s1;
							else
								switchDefault =
									new StSequence(
										switchDefault,
										switchDefault,
										s1);
						}
					}
				}
			}
			subtree = subtree.getNextSibling();
		}
		// If no default case is defined, a default skip statement is assign to
		// the default case.
		if (beforeDefault) {
			switchDefault = new StSkip();
		}
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		if (switchCase1 != null)
			switchCase1.linkStatement(config, f);
		switchDefault.linkStatement(config, f);
		if (switchCase2 != null)
			switchCase2.linkStatement(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (switchCase1 != null)
			switchCase1.typeCheck(config, f);
		switchDefault.typeCheck(config, f);
		if (switchCase2 != null)
			switchCase2.typeCheck(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		exp = (Expression) exp.jmlNormalize(config, definingClass);
		if (switchCase1 != null)
			switchCase1 = switchCase1.jmlNormalize(config, definingClass);
		switchDefault =
			(Statement) switchDefault.jmlNormalize(config, definingClass);
		if (switchCase2 != null)
			switchCase2 = switchCase2.jmlNormalize(config, definingClass);
		return this;
	}

	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {

		// vv is the tempory variable that strores switch expression evaluation
		String vv = fresh();

		// If a case body terminates abruplty on a break, the 
		// normal behaviour should be proved.
		finishOnBreakLab.add(null, (Proofs) normalBehaviour.clone());

		// Proof of the default case
		Proofs lv1 =
			CasesList.sequence(switchDefault, switchCase2).wp(
				config,
				normalBehaviour,
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);

		// Add hypothesis concerning the negation of all existing cases
		if (switchCase1 != null || switchCase2 != null) {
			FormulaWithSpecMethodDecl tmp = switchDefault(config, vv, switchCase1, switchCase2);
			//@ assert tmp != null;

			lv1.addHyp(
				FormulaWithSpecMethodDecl.not(tmp),
				new ColoredInfo(switchDefault),
				VirtualFormula.LOCALES);
		}

		// Proof of all the cases that are before the default one
		if (switchCase1 != null)
			lv1.addAll(
				switchCase1.switchBeforeDefault(
					config,
					vv,
					switchDefault,
					switchCase2,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));

		// Proof of all the cases that are after the default one
		if (switchCase2 != null)
			lv1.addAll(
				switchCase2.switchAfterDefault(
					config,
					vv,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));

		// Remove the proof associated to the termination on a break.
		finishOnBreakLab.remove();

		return exp.wp(config, vv, lv1, exceptionalBehaviour);

	}

	static final long serialVersionUID = 2677107039781057404L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		exp.getPrecondition(config, modifies, req, ens);
		if (switchCase1 != null) {
			CasesList tmp = switchCase1;
			while (tmp != null) {
				tmp.getBody().getPrecondition(config, modifies, req, ens);
				tmp = tmp.getNext();
			}
		}
		switchDefault.getPrecondition(config, modifies, req, ens);
		if (switchCase2 != null) {
			CasesList tmp = switchCase2;
			while (tmp != null) {
				tmp.getBody().getPrecondition(config, modifies, req, ens);
				tmp = tmp.getNext();
			}
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		exp.collectCalledMethod(calledMethod);
		if (switchCase1 != null) {
			CasesList tmp = switchCase1;
			while (tmp != null) {
				tmp.getBody().collectCalledMethod(calledMethod);
				tmp = tmp.getNext();
			}
		}
		switchDefault.collectCalledMethod(calledMethod);
		if (switchCase2 != null) {
			CasesList tmp = switchCase2;
			while (tmp != null) {
				tmp.getBody().collectCalledMethod(calledMethod);
				tmp = tmp.getNext();
			}
		}
	}

	public void getAssert(Vector asser) {
		exp.getAssert(asser);
		if (switchCase1 != null) {
			CasesList tmp = switchCase1;
			while (tmp != null) {
				tmp.getBody().getAssert(asser);
				tmp = tmp.getNext();
			}
		}
		switchDefault.getAssert(asser);
		if (switchCase2 != null) {
			CasesList tmp = switchCase2;
			while (tmp != null) {
				tmp.getBody().getAssert(asser);
				tmp = tmp.getNext();
			}
		}
	}

	public void getSpecBlock(Vector blocks) {
		exp.getSpecBlock(blocks);
		if (switchCase1 != null) {
			CasesList tmp = switchCase1;
			while (tmp != null) {
				tmp.getBody().getSpecBlock(blocks);
				tmp = tmp.getNext();
			}
		}
		switchDefault.getSpecBlock(blocks);
		if (switchCase2 != null) {
			CasesList tmp = switchCase2;
			while (tmp != null) {
				tmp.getBody().getSpecBlock(blocks);
				tmp = tmp.getNext();
			}
		}
	}

	public void getLoop(Vector loops) {
		exp.getLoop(loops);
		if (switchCase1 != null) {
			CasesList tmp = switchCase1;
			while (tmp != null) {
				tmp.getBody().getLoop(loops);
				tmp = tmp.getNext();
			}
		}
		switchDefault.getLoop(loops);
		if (switchCase2 != null) {
			CasesList tmp = switchCase2;
			while (tmp != null) {
				tmp.getBody().getLoop(loops);
				tmp = tmp.getNext();
			}
		}
	}

}
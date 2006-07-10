//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ExceptionalBehaviourStack.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.substitution.SubTypeofSingle;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.AMethod;
import jml2b.structure.java.AClass;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;
import jml2b.structure.statement.TerminalExp;
import jml2b.util.Profiler;

/**
 * This class describes a stack of proof obligations associated to exceptional
 * behaviours.
 * @author L. Burdy
 **/
public class ExceptionalBehaviourStack extends Profiler implements IFormToken {

	private static Enumeration getDefaultExsures(IJml2bConfiguration config)
		throws Jml2bException {
		Vector tmp = new Vector();
		tmp.add(
			new Exsures(
				new Type(
					((JavaLoader) config.getPackage()).getJavaLang().getAndLoadClass(config, "Exception")),
				(String) null,
				new TerminalExp(
					JmlDeclParserTokenTypes.LITERAL_false,
					"FALSE")));
		return tmp.elements();
	}

	public static ExceptionalBehaviourStack getFalse(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		return new ExceptionalBehaviourStack(
			new ExceptionalProofs(
				new Theorem(
					config,
					getDefaultExsures(config),
					null,
					new GoalOrigin(GoalOrigin.WELL_DEFINED))));
	}

	/**
	 * The proof on top of the stack.
	 **/
	private ExceptionalProofs eb;

	/**
	 * The next element of the stack
	 **/
	private ExceptionalBehaviourStack next;

	/*@
	  @ private invariant eb != null;
	  @*/

	/**
	 * Constructs a stack with one element.
	 * @param eb The element on top of the stack
	 **/
	/*@
	  @ requires eb != null;
	  @*/
	public ExceptionalBehaviourStack(ExceptionalProofs eb) {
		this.eb = eb;
		next = null;
	}

	/**
	 * Constructs a stack from another stack.
	 * @param eb The element on top of the stack
	 * @param next The next element
	 **/
	/*@
	  @ requires eb != null;
	  @*/
	private ExceptionalBehaviourStack(
		ExceptionalProofs eb,
		ExceptionalBehaviourStack next) {
		this.eb = eb;
		this.next = next;
	}

	/**
	 * Clones the stack
	 * @return the cloned stack
	 **/
	public Object clone() {
		return new ExceptionalBehaviourStack(
			(ExceptionalProofs) eb.clone(),
			next == null ? null : (ExceptionalBehaviourStack) next.clone());
	}

	/**
	 * Returns the size of the stack
	 * @return the number of element of the stack
	 **/
	public int size() {
		if (next == null)
			return 1;
		else
			return 1 + next.size();
	}

	/**
	 * Push an element on top of the stack
	 * @param eb The proof to push
	 * @return the new stack
	 **/
	public ExceptionalBehaviourStack push(ExceptionalProofs eb) {
		return new ExceptionalBehaviourStack(eb, this);
	}

	/**
	 * Pop elements from the stack
	 * @param i The number of elements to pop
	 * @return the new stack
	 **/
	public ExceptionalBehaviourStack pop(int i) {
		if (i == 0)
			return this;
		else
			return next.pop(i - 1);
	}

	/**
	 * Concats two stacks.
	 * @param ebs The stack to concat to the current one
	 * @return a stack consisting on the two stacks concatened
	 **/
	public ExceptionalBehaviourStack addAll(ExceptionalBehaviourStack ebs) {
		if (ebs.next == null) {
			ebs.next = this;
		} else {
			ebs.next = addAll(ebs.next);
		}
		return ebs;
	}

	/**
	 * Returns the proof to prove to ensure that the thrown of an exception 
	 * ensures the current proof.
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	public Proofs throwException(Formula vv, Formula c) {
		Proofs res = new Proofs();
		if (next != null) {
			res = next.throwException(vv, c);
		}
		Formula tmp;
		if ((tmp = eb.notSubTypesException(c)) != null)
			res.addHyp(tmp);
		res.addAll(eb.throwException(vv, c));
		return res;
	}

	/**
	 * Returns the proof obligation ensuring that the thrown of an exception 
	 * ensures the current proof.
	 * @param vv The instance of the thrown exception.
	 * @param c  The class of the thrown exception.
	 */
	public Proofs throwException(String vv, AClass c) {
		if (next != null && !eb.catches(c))
			return next.throwException(vv, c);
		Proofs res = new Proofs();
		res.addAll(eb.throwException(vv, c));
		return res;
	}

	/**
	 * Calculates the proof obligation ensuring that the thrown of a runtime 
	 * exception ensures the current proof.
	 * @param config The current configuration
	 * @param c The class of the thrown exception.
	 * @throws PogException
	 **/
	public Proofs throwException(IJml2bConfiguration config, AClass c)
		throws Jml2bException, PogException {
		// oo is the new object.
		String oo = Statement.freshObject();

		// t corresponds to the OP associated with the throw of this exception.
		Proofs t = throwException(oo, c);

		// m is the default constructor of the exception
		AMethod m = c.getSuperDefaultConstructor();

		Formula s1, s2;
		// s1 contains the object on witch the method is called.
		s1 = new TerminalForm(oo);
		// s2 contains the formula "this"
		s2 = new TerminalForm(Ja_LITERAL_this, "this");

		Proofs res = new Proofs();
		Enumeration e = m.getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase sc = (SpecCase) e.nextElement();
			Proofs tmp = (Proofs) t.clone();

			Expression ens = (Expression) sc.getEnsures().clone();
			ens.old();
			FormulaWithSpecMethodDecl ensures = ens.predToForm(config).sub(s2, s1, false);

			Theorem localExsures =
				new Theorem(
					config,
					sc.getExsures(),
					null,
					new GoalOrigin(GoalOrigin.EXSURES, m));

			Proofs exsures = localExsures.impliesExceptional(this);
			exsures.sub(new SubForm(s2, s1));
			tmp.addHyp(ensures, new ColoredInfo(m), VirtualFormula.ENSURES);

			tmp.addAll(exsures);

			ModifiesClause modifies = sc.getModifies();
			if (modifies != null)
				tmp = modifies.modifies(config, m, tmp);
			res.addAll(tmp);
		}

		Expression req = (Expression) m.getNormalizedRequires(config).clone();
		req.old();
		SimpleLemma requires =
			new SimpleLemma(
				config,
				req,
				new GoalOrigin(GoalOrigin.REQUIRES, m));
		requires.sub(new SubForm(s2, s1));

		res.addAll(new Proofs(requires));
		res.suppressSpecialOld(IFormToken.T_CALLED_OLD);

		// typeof := typeof <+ {oo |-> \type(c)}
		res.sub(
			new SubTypeofSingle(
				new TerminalForm(oo),
				new TTypeForm(IFormToken.Jm_T_TYPE, new Type(c))));

		res.addHyp(BinaryForm.getDefaultRefDecl(new TerminalForm(oo)));
		return res.quantify(oo, TerminalForm.$References);
	}

	/**
	 * Calculate the ExceptionalProofs stack resulting from the application of  
	 * the body on the current stack (used to proceed a <i>finally</i>).
	 * @param config The current configuration
	 * @param body The finally body
	 * @param finishOnReturn theorems to ensure if the statement terminates
	 * abruptly on a <code>return</code>
	 * @param finishOnBreakLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>break</code>
	 * @param finishOnContinueLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>continue</code>
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * statement terminates abruply on an exception
	 * @return the new stack
	 * @throws PogException
	 */
	public ExceptionalBehaviourStack finallyOnExceptionalBehaviour(
		IJml2bConfiguration config,
		Statement body,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		if (next == null) {
			return new ExceptionalBehaviourStack(
				eb.finallyOnExceptionalBehaviour(
					config,
					body,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));
		} else
			return new ExceptionalBehaviourStack(
				eb.finallyOnExceptionalBehaviour(
					config,
					body,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour),
				next.finallyOnExceptionalBehaviour(
					config,
					body,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour));
	}

}

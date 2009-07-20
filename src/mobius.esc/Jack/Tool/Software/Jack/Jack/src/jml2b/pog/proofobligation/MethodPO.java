//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: MethodPO
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package jml2b.pog.proofobligation;

import java.util.Enumeration;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.AMethod;
import jml2b.structure.java.Class;
import jml2b.structure.java.*;
import jml2b.structure.statement.Statement;

/**
 * This class describes proof obligations for a method and facilities to
 * calculate them.
 * 
 * @author L. Burdy
 */
public class MethodPO extends SourceProofObligation {

	/**
	 * The current method
	 */
	private Method method;

	/**
	 * The invariant to respect
	 */
	private FormulaWithSpecMethodDecl invariant;

	/**
	 * The requires of the current method
	 */
	private FormulaWithSpecMethodDecl requires;

	/*
	 * @ @ private invariant method != null @ && invariant != null @ && requires !=
	 * null; @
	 */

	/**
	 * Constructs a proof obligation
	 * 
	 * @param name
	 *            The lemmas name
	 * @param c
	 *            The current class
	 * @param m
	 *            The current method
	 * @param h1
	 *            The invariant
	 * @param h2
	 *            The requires
	 * @param box
	 *            The colored info
	 * @param b
	 *            The body
	 * @param p1
	 *            The normal behaviour proof
	 * @param p7
	 *            The exceptional behaviour proof
	 */
	/*
	 * @ @ requires m != null && h1 != null && h2 != null; @
	 */
	MethodPO(String name, Class c, Method m, FormulaWithSpecMethodDecl h1, FormulaWithSpecMethodDecl h2, ColoredInfo box, Statement b, Theorem p1,
			Theorem p7) {
		super(name, b, p1, p7, c, box);
		method = m;
		method.setPmiName(name);
		invariant = h1;
		requires = h2;
	}

	/**
	 * Constructs a proof obligation
	 * 
	 * @param c
	 *            The current class
	 * @param m
	 *            The current method
	 * @param h1
	 *            The invariant
	 * @param h2
	 *            The requires
	 * @param box
	 *            The colored info
	 * @param b
	 *            The body
	 * @param p1
	 *            The normal behaviour proof
	 * @param p7
	 *            The exceptional behaviour proof
	 */
	/*
	 * @ @ requires m != null && h1 != null && h2 != null; @
	 */
	public MethodPO(Class c, Method m, FormulaWithSpecMethodDecl h1, FormulaWithSpecMethodDecl h2, ColoredInfo box, Statement b, Theorem p1, Theorem p7) {
		this(c.getBName() + "_method_" + ++methodCount + "_" + m.getName(), c, m, h1, h2, box, b, p1, p7);
	}

	/**
	 * Process the WP calculus on the proof obligations. Add the hypothesis
	 * concerning the typing of <code>this</code> and finalize the calculated
	 * lemmas.
	 */
	public void pog(IJml2bConfiguration config) throws Jml2bException, PogException {
		ExceptionalBehaviourStack ebs = new ExceptionalBehaviourStack(new ExceptionalProofs(getPhi7()));

		// Processes the WP calculus for the method body
		if(getBody() != null) {
			method.lemmas = getBody().ensures(config, getPhi1(), ebs, ((Parameters) method.getParams()).signature);
		}
		else {//specification method case
			method.lemmas = new Proofs();
		}
		
		// Adds the hypothese this : instances
		method.lemmas.addHyp(new BinaryForm(LOCAL_VAR_DECL, new TerminalForm(Ja_LITERAL_this, "this"),
				TerminalForm.$References));
		method.lemmas.addHyp(new BinaryForm(B_IN, new TerminalForm(Ja_LITERAL_this, "this"), TerminalForm.$instances));

		// Adds the hypothese typeof(this) <: class
		method.lemmas.addHyp(new BinaryForm(Jm_IS_SUBTYPE, new BinaryForm(B_APPLICATION, TerminalForm.$typeof,
				new TerminalForm(Ja_LITERAL_this, "this")), new TTypeForm(IFormToken.Jm_T_TYPE, new Type(method
				.getDefiningClass()))));

		// If the method returns a value, subsitute \result with NORESULT to
		// allow type cheking.
		if (method.getReturnType() != null && method.getReturnType().getTag() != Type.T_VOID)
			method.lemmas.sub(new SubForm(new TerminalForm(Jm_T_RESULT, "\result"), new TerminalForm("NORESULT")));

		// Finalize the lemmas
		finalizePog(config);
	}

	/**
	 * Finalize the proof obligations by
	 * <UL>
	 * <li> adding the proof of the requires of the super method if it exists
	 * <li> adding the parameters typing in hypothesis
	 * <li> adding the invariant coming from the final static field
	 * initialization in hypothesis
	 * <li> adding the invariant in hypothesis
	 * <li> adding the requires of the current method in hypothesis
	 * <li> assigning a name
	 * </UL>
	 */
	final void finalizePog(IJml2bConfiguration config) throws Jml2bException, PogException {
//		Formula pureMethodDecl;
		AMethod superM = method.getSuperMethod(config);
		if (superM != null) {
			SimpleLemma req = new SimpleLemma(config, method.getNormalizedRequires(config), new GoalOrigin(
					GoalOrigin.SUPER_REQUIRES));
			Proofs reqP = new Proofs(req);
			reqP.addHyp(superM.getNormalizedRequires(config).predToForm(config),
						new ColoredInfo(superM),
						VirtualFormula.REQUIRES);
			method.lemmas.addAll(reqP);
		}
//		if ((pureMethodDecl =getPureMethodDecl(config)) == null)
//			pureMethodDecl = new TerminalForm(B_BTRUE, "(0=0)");

		method.lemmas.finalize(	config,
								parameterDeclaration(method),
								getCl().getStaticFinalFieldsInvariants((JavaLoader) config.getPackage()),
//								pureMethodDecl,
								invariant,
								requires,
								getName(),
								getBox(),
								new ColoredInfo(method, ColoredInfo.METHOD_CALL, method.getInfo()));
	}

	/**
	 * Returns the formula corresponding to the parameter declaration of the
	 * method.
	 */
	public static Formula parameterDeclaration(Method method) {
		Formula res = null;
		Enumeration e = ((Parameters) method.getParams()).signature.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			Formula fo = Formula.declarField(f);
			if (res == null) {
				res = fo;
			} else
				res = Formula.and(res, fo);
		}
		return res;
	}

	public void proveObvious(boolean prove) {
		method.lemmas.proveObvious(prove, true);
	}

	/**
	 * Returns the currentmethod.
	 * 
	 * @return <code>method</code>
	 */
	public Method getMethod() {
		return method;
	}

	public String getDisplayedName() {
		return method.getName() + method.getSignature();
	}

}

//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: NormalizedGuardedModifies
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.statement.Expression;

/**
 * This class implements a guarded modifies that has been normalized. The guard
 * has been converted to a formula.
 * @author L. Burdy
 **/
class NormalizedGuardedModifies extends GuardedModifies {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * The guard of the modifies clause as a formula
	 **/
	private FormulaWithPureMethodDecl guardF;

	/*@
	  @ private invariant guardF != null;
	  @*/

	/**
	 * Constructs a normalized guarded modifies.
	 * @param m The store-ref
	 * @param f The guard
	 **/
	/*@
	  @ requires f != null;
	  @*/
	NormalizedGuardedModifies(Modifies m, FormulaWithPureMethodDecl f) {
		super(m, (Expression) null);
		guardF = f;
	}

	/**
	 * Constructs a normalized guarded modifies from another one by concatening 
	 * the guards.
	 * @param gm The normalized guarded modifies
	 * @param f The guard
	 **/
	/*@
	  @ requires f != null;
	  @*/
	private NormalizedGuardedModifies(NormalizedGuardedModifies gm, FormulaWithPureMethodDecl f)
		throws PogException {
		super(gm.getM(), (Expression) null);
		guardF = FormulaWithPureMethodDecl.and(gm.guardF, f);
	}

	/**
	 * Constructs a normalized guarded modifies from another one.
	 * @param m The guarded modifies
	 * @param e The guard as an expression
	 * @param f The guard as a formula
	 **/
	/*@
	  @ requires f != null;
	  @*/
	NormalizedGuardedModifies(Modifies m, Expression e, FormulaWithPureMethodDecl f) {
		super(m, e);
		guardF = f;
	}

	/**
	 * Clones the normalized guarded modified.
	 * @return the cloned normalized guarded modified
	 **/
	public Object clone() {
		return new NormalizedGuardedModifies(
			(Modifies) getM().clone(),
			getGuardE() == null ? null : (Expression) getGuardE().clone(),
			(FormulaWithPureMethodDecl) guardF.clone());
	}

	/**
	 * Return the modifies list with modified store-ref issued from a depends 
	 * clause.
	 * @param d The depends clause
	 **/
	ModifiesList addDepends(IJml2bConfiguration config, Depends d)
		throws PogException {
		Vector fo = getM().addDepends(config, d);
		if (fo.size() <= 0)
			return null;
		ModifiesList ml = null;
		Enumeration e = fo.elements();
		while (e.hasMoreElements()) {
			Object m = e.nextElement();
			if (m instanceof Modifies) {
				if (ml == null)
					ml =
						new ModifiesList(
							new NormalizedGuardedModifies((Modifies) m, guardF),
							null);
				else
					ml.addModifies(
						new NormalizedGuardedModifies((Modifies) m, guardF));
			} else {
				if (ml == null)
					ml =
						new ModifiesList(
							new NormalizedGuardedModifies(
								(NormalizedGuardedModifies) m,
								guardF),
							null);
				else
					ml.addModifies(
						new NormalizedGuardedModifies(
							(NormalizedGuardedModifies) m,
							guardF));
			}
		}
		return ml;
	}

	/**
	 * Substitutes two fields.
	 * @param a The field to substitute
	 * @param b The new field
	 * @return The substituted normalized guarded modifies
	 * @throws PogException
	 **/
	NormalizedGuardedModifies sub(IJml2bConfiguration config, Field a, Field b)
		throws PogException {
		return new NormalizedGuardedModifies(
			getM().sub(config, a, b),
			getGuardE(),
			guardF.sub(a, b, true));
	}

	/** 
	 * Replace <code>this</code> with the parameter in the <i>modifies clause</i>.
	 * @param b expression on which the method is called.
	 **/
	void instancie(IJml2bConfiguration config, Expression b)
		throws PogException {
		getM().instancie(b);
		try {
			FormulaWithPureMethodDecl fwp = b.predToForm(config);
			FormulaWithPureMethodDecl fwp1 = guardF.instancie(fwp.getFormula());
			guardF = new FormulaWithPureMethodDecl(fwp, fwp1, fwp1.getFormula());
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}

	}

	/**
	 * Returns whether the guard is relevant
	 * @return <code>true</code> if the guard is not btrue, <code>false</code> 
	 * otherwise
	 **/
	boolean hasRelevantGuard() throws PogException {
		return guardF.getFormula().getNodeType() != IFormToken.B_BTRUE;
	}

	/**
	 * Returns the formula corresponding to the restriction to be applied to
	 * a member field restricted to the current instances set.
	 * @param f The field to restrict.
	 * @return the restriction to applied to the domain of the member field.
	 **/
	FormulaWithPureMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f)
		throws PogException {
		FormulaWithPureMethodDecl fo = getM().getModifiedInstances(config, f);
		if (fo == null || !hasRelevantGuard())
			return fo;
		else {
			
			return new FormulaWithPureMethodDecl(fo, guardF, new BinaryForm(IFormToken.GUARDED_SET, fo.getFormula(), guardF.getFormula()));
	}
	}

	/**
	 * Returns the formula corresponding to the restriction to be applied to 
	 * the variable xxxelements with type corresponding to tag.
	 * @param tag: tag of the xxxelements to restrict.
	 * @return a restriction to applied to the domain of the corresponding
	 * xxxelements variable.
	 * @throws PogException
	 **/
	FormulaWithPureMethodDecl restrictElement(IJml2bConfiguration config, int tag)
		throws PogException {
		FormulaWithPureMethodDecl fo = getM().restrictElement(config, tag);
		if (fo == null || !hasRelevantGuard())
			return fo;
		else
			return new FormulaWithPureMethodDecl(fo, guardF, new BinaryForm(IFormToken.GUARDED_SET, fo.getFormula(), guardF.getFormula()));
	}

	/**
	 * Return the formula corresponding to the restriction to be applied to
	 * the domain of the <code>xxxelements(f)</code> function.
	 * @param f The array instance to restrict.
	 * @return the restriction to applied to the domain of 
	 * <code>xxxelements(f)</code>.
	 * @throws PogException
	 **/
	FormulaWithPureMethodDecl getModifiedIndexes(IJml2bConfiguration config, int tag, Formula q)
		throws PogException {
		FormulaWithPureMethodDecl fo = getM().getModifiedIndexes(config, tag, q);
		if (fo == null || !hasRelevantGuard())
			return fo;
		else
			return new FormulaWithPureMethodDecl(fo, guardF, new BinaryForm(IFormToken.GUARDED_SET, fo.getFormula(), guardF.getFormula()));
	}

	/**
	 * Returns the guard.
	 * @return <code>guardF</code>
	 */
	FormulaWithPureMethodDecl getGuardF() {
		return guardF;
	}

}
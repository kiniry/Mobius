//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesLbrack.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TriaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class implements a modifies corresponding to array elements, that is
 * <code>a[b], a[b..c]</code> or <code>a[*]</code> where <code>a, b</code>
 * and <code>c</code> are expressions.
 * @author L. Burdy
 **/
public class ModifiesLbrack extends Modifies {

	/**
	 * The indexes of modified element.
	 **/
	private SpecArray sa;

	/**
	 * The array where element are modified
	 **/
	private Modifies m;

	/*@
	  @ private invariant sa != null;
	  @ private invariant m != null;
	  @*/

	/**
	 * Constructs an empty modified variable corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesLbrack(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		m = Modifies.create(jf, tree.getFirstChild());
		sa = SpecArray.create(jf, tree.getFirstChild().getNextSibling());
	}

	/**
	 * Constructs a modified array from another one.
	 * @param pi The parsed item
	 * @param t The type of the field
	 * @param sa The set of array indexes
	 * @param m The modified array
	 **/
	/*@
	  @ requires sa != null && m != null;
	  @*/
	private ModifiesLbrack(ParsedItem pi, Type t, SpecArray sa, Modifies m) {
		super(pi, t);
		this.sa = sa;
		this.m = m;
	}

	/**
	 * Constructs a modifies corresponding to <code>f[*]</code>.
	 * @param f The modified array field
	 **/
	ModifiesLbrack(Field f) {
		super(f, f.getType());
		m = new ModifiesDot(f, new Identifier(f));
		sa = new SpecArrayStar(f);
	}

	public Object clone() {
		return new ModifiesLbrack(
			this,
			getStateType(),
			(SpecArray) sa.clone(),
			(Modifies) m.clone());
	}

	Vector getParsedItems() {
		Vector res = sa.getParsedItems();
		res.addAll(m.getParsedItems());
		return res;
	}

	void setParsedItem(ParsedItem pi) {
		sa.setParsedItem(pi);
		m.setParsedItem(pi);
	}

	/**
	 * @return <code>xxxelements(m)(sa)</code>
	 * @throws InternalError when <code>m</code> or <code>sa</code> cannot be
	 * converted into singleton.
	 **/
	FormulaWithPureMethodDecl getFormula(IJml2bConfiguration config) throws PogException {
		if (sa instanceof SpecArrayExpr) {
			FormulaWithPureMethodDecl fwp = m.getFormula(config);
			FormulaWithPureMethodDecl fwp1 = sa.getFormula(config);
			return new FormulaWithPureMethodDecl(fwp, fwp1,
		new BinaryForm(
			IFormToken.ARRAY_ACCESS,
			new BinaryForm(
				IFormToken.B_APPLICATION,
				ElementsForm.getElementsName(m.getStateType().getElemType()),
				fwp.getFormula()),
			fwp1.getFormula()));
		}
		else {
			FormulaWithPureMethodDecl fwp = m.getSet(config);
			FormulaWithPureMethodDecl fwp1 = sa.getSet(config, m);
			return new FormulaWithPureMethodDecl(fwp, fwp1,
			new TriaryForm(
									ARRAY_RANGE,
									ElementsForm.getElementsName(m.getStateType().getElemType()),
									fwp.getFormula(),
									fwp1.getFormula()));
	}
	}

	/**
	 * @return <code>UNION(x).(x : m | elements(x)[sa])</code>
	 **/
	FormulaWithPureMethodDecl getSet(IJml2bConfiguration config) throws PogException {
		FormulaWithPureMethodDecl fwp = m.getSet(config);
		FormulaWithPureMethodDecl fwp1 = sa.getSet(config, m);
		return new FormulaWithPureMethodDecl(fwp, fwp1, new TriaryForm(
			ARRAY_RANGE,
			ElementsForm.getElementsName(m.getStateType().getElemType()),
			fwp.getFormula(),
			fwp1.getFormula()));
	}

	LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkInfo res = m.linkStatements(config, f);
		sa.linkStatement(config, f);
		if (res.tag == LinkInfo.TYPE) {
			setStateType(res.getType().getElemType());
			res = new LinkInfo(res.getType().getElemType());
		}
		return res;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		m.typeCheck(config, f);
		sa.typeCheck(config, f);
		return null;
	}

	Modifies instancie() {
		sa = (SpecArray) sa.instancie();
		m = m.instancie();
		return this;
	}

	void instancie(Expression b) {
		sa.instancie(b);
		m.instancie(b);
	}

	boolean is(AField f) {
		return m.is(f);
	}

	/**
	 * @return <code>null</code>
	 **/
	FormulaWithPureMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f) {
		return null;
	}

	/**
	 * @return m if the modified array has the searched for tag.
	 **/
	FormulaWithPureMethodDecl restrictElement(IJml2bConfiguration config, int tag)
		throws PogException {
		if (getStateType().getTag() == tag) {
			return m.getSet(config);
		} else
			return null;
	}

	FormulaWithPureMethodDecl getModifiedIndexes(IJml2bConfiguration config, int tag, Formula q)
		throws PogException {
		if (getStateType().getTag() == tag) {
			FormulaWithPureMethodDecl fwp = getRange(config);
			FormulaWithPureMethodDecl fwp1 = m.getSet(config);
			return new FormulaWithPureMethodDecl(fwp, fwp1,
			 new BinaryForm(
				IFormToken.GUARDED_SET,
				fwp.getFormula(),
				new BinaryForm(IFormToken.B_IN, q, fwp1.getFormula())));
		} else
			return null;
	}

	/**
	 * Returns the formula correspondig to the set of mmodified index
	 * @param config The current configuration
	 * @return the formula correspondig to the set of mmodified index
	 * @throws PogException
	 */
	private FormulaWithPureMethodDecl getRange(IJml2bConfiguration config) throws PogException {
		return sa.getSet(config, m);
	}

	/**
	 * If the depends store ref is an instanciated array, the dependees are 
	 * added with a guard corresponding to
	 * <code>m /\ m' != {} && sa /\ sa' != null </code>.
	 * If the depends store ref is a non instanciated array, the instanciated 
	 * dependees are added with a guard corresponding to
	 * <code>m /\ m' != {} && sa /\ sa' != null </code>.
	 * Otherwise no store ref are added.
	 **/
	Vector addDepends(IJml2bConfiguration config, Depends d)
		throws PogException {
		Vector res = new Vector();
		Modifies m = d.getAbstractField();
		if (m instanceof ModifiesLbrack) {
			if (!m.isMemberNonInstanciated()) {
				Enumeration e = d.getConcreteFields().elements();
				while (e.hasMoreElements()) {
					Modifies mo =
						(Modifies) ((Modifies) e.nextElement()).clone();
					FormulaWithPureMethodDecl fwp1 =this.m.getSet(config);
					FormulaWithPureMethodDecl fwp2 =((ModifiesLbrack) m).getM().getSet(config);
					FormulaWithPureMethodDecl fwp3 =getRange(config);
					FormulaWithPureMethodDecl fwp4 =((ModifiesLbrack) m).getRange(config);
					// m/\m' != {} && sa/\sa' != {} 
					res.add(
						new NormalizedGuardedModifies(
							mo,
							FormulaWithPureMethodDecl.and(
								new FormulaWithPureMethodDecl(fwp1, fwp2,
								new BinaryForm(
									INTERSECTION_IS_NOT_EMPTY,
									fwp1.getFormula(),
									fwp2.getFormula())),
									new FormulaWithPureMethodDecl(fwp3, fwp4,
								new BinaryForm(
									INTERSECTION_IS_NOT_EMPTY,
									fwp3.getFormula(),
									fwp4.getFormula())))));
				}
			} else {
				if (is(m.getField())) {
					m = (Modifies) m.clone();
					Expression ex = getInstanciation();
					m.instancie(ex);
					Enumeration e = d.getConcreteFields().elements();
					while (e.hasMoreElements()) {
						Modifies mo =
							(Modifies) ((Modifies) e.nextElement()).clone();
						mo = mo.instancie();
						mo.instancie(ex);
						// 
						FormulaWithPureMethodDecl fwp1 =this.m.getSet(config);
						FormulaWithPureMethodDecl fwp2 =((ModifiesLbrack) m).getM().getSet(config);
						FormulaWithPureMethodDecl fwp3 =getRange(config);
						FormulaWithPureMethodDecl fwp4 =((ModifiesLbrack) m).getRange(config);
						res.add(
							new NormalizedGuardedModifies(
								mo,
								FormulaWithPureMethodDecl.and(
								                              new FormulaWithPureMethodDecl(fwp1, fwp2,
									new BinaryForm(
										INTERSECTION_IS_NOT_EMPTY,
										fwp1.getFormula(),
										fwp2.getFormula())),
										new FormulaWithPureMethodDecl(fwp3, fwp4,
									new BinaryForm(
										INTERSECTION_IS_NOT_EMPTY,
										fwp3.getFormula(),
										fwp4.getFormula())))));
					}
				}
			}
		}
		return res;
	}

	Modifies sub(IJml2bConfiguration config, Field a, Field b)
		throws PogException {
		SpecArray newSa = sa.sub(config, this, a, b);
		return new ModifiesLbrack(
			this,
			getStateType(),
			newSa,
			m.sub(config, a, b));
	}

	void processIdent() {
		sa.processIdent();
		m.processIdent();
	}

	/**
	 * Returns the modified variable.
	 * @return <code>m</code>
	 */
	public Modifies getM() {
		return m;
	}

	AField getField() {
		return m.getField();
	}

	Expression getInstanciation() {
		return m.getInstanciation();
	}

	boolean isMemberNonInstanciated() {
		return m.isMemberNonInstanciated();
	}

	static final long serialVersionUID = -2052379372104415120L;

	public boolean equals(IJml2bConfiguration config, Modifies m) {
		return m instanceof ModifiesLbrack
			&& ((ModifiesLbrack) m).sa.equals(sa) 
			&& ((ModifiesLbrack) m).m.equals(config, this.m);
	}

	/**
	 * @return
	 */
	public SpecArray getSa() {
		return sa;
	}

}

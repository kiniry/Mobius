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
import jml2b.formula.IModifiesField;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;
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
	FormulaWithSpecMethodDecl getFormula(IJml2bConfiguration config) throws PogException {
		if (sa instanceof SpecArrayExpr) {
			FormulaWithSpecMethodDecl fwp = m.getFormula(config);
			FormulaWithSpecMethodDecl fwp1 = sa.getFormula(config);
			return new FormulaWithSpecMethodDecl(fwp, fwp1,
		new BinaryForm(
			IFormToken.ARRAY_ACCESS,
			new BinaryForm(
				IFormToken.B_APPLICATION,
				ElementsForm.getElementsName(m.getStateType().getElemType()),
				fwp.getFormula()),
			fwp1.getFormula()));
		}
		else {
			FormulaWithSpecMethodDecl fwp = m.getSet(config);
			FormulaWithSpecMethodDecl fwp1 = sa.getSet(config, m);
			return new FormulaWithSpecMethodDecl(fwp, fwp1,
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
	FormulaWithSpecMethodDecl getSet(IJml2bConfiguration config) throws PogException {
		FormulaWithSpecMethodDecl fwp = m.getSet(config);
		FormulaWithSpecMethodDecl fwp1 = sa.getSet(config, m);
		return new FormulaWithSpecMethodDecl(fwp, fwp1, new TriaryForm(
			ARRAY_RANGE,
			ElementsForm.getElementsName(m.getStateType().getElemType()),
			fwp.getFormula(),
			fwp1.getFormula()));
	}

	/**
	 * @return <code>m[sa]</code>
	 **/
	String toJava(int indent) {
		return m.toJava(indent) + "[" + sa.toJava(indent) + "]";
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

	/**
	 * @return
	 * <code> \forall type newName;
	 *          {m} <<| newName == {m} <<| elements
	 *          && dom(newName) == dom(elements) 
	 *          && right <<| newName(m) == right <<| elements(m)
	 *          ==> [elements := newName]s</code>
	 **/
	Proofs applyMod(IJml2bConfiguration config, IModifiesField me, Proofs s)
		throws PogException {
		jml2b.formula.ElementsForm elements =
			ElementsForm.getElementsName(getStateType());
		TerminalForm newName = new ElementsForm(elements);

		FormulaWithSpecMethodDecl fwp = m.getSet(config);
		// f2 = dom(newName) == dom(elements) && 
		//      {m} <<| newName == {m} <<| elements
		FormulaWithSpecMethodDecl f2 =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				B_SUBSTRACTION_DOM,
				fwp.getFormula(),
				new BinaryForm(B_FUNCTION_EQUALS, newName, elements)));

		TerminalForm xx = new TerminalForm(Statement.fresh());

		Proofs res = s.sub(new SubForm(elements, newName));
		//		res.addHyp(f1);
		res.addHyp(f2);

		if (!(sa instanceof SpecArrayStar)) {
			fwp = m.getSet(config);
			FormulaWithSpecMethodDecl fwp1 = sa.getSet(config, m);
			// f3 = !xx.(xx : REFERENCES && xx : m 
			//           ==> right <<| newName(xx) == right <<| elements(xx)
			FormulaWithSpecMethodDecl f3 =
				new FormulaWithSpecMethodDecl(fwp, fwp1,
				new QuantifiedForm(
					Jm_FORALL,
					new QuantifiedVarForm(xx, TerminalForm.$References),
					new BinaryForm(
						Jm_IMPLICATION_OP,
						new BinaryForm(B_IN, xx, fwp.getFormula()),
						new BinaryForm(
							B_SUBSTRACTION_DOM,
							fwp1.getFormula(),
							new TriaryForm(
								B_ARRAY_EQUALS,
								xx,
								newName,
								elements)))));
			res.addHyp(f3);
		}
		res.addHyp(
				new BinaryForm(LOCAL_ELEMENTS_DECL, newName, elements.getType()),
				new ColoredInfo(),
				VirtualFormula.LOCALES);
		return res;
	}

	boolean is(AField f) {
		return m.is(f);
	}

	/**
	 * @return <code>null</code>
	 **/
	FormulaWithSpecMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f) {
		return null;
	}

	/**
	 * @return m if the modified array has the searched for tag.
	 **/
	FormulaWithSpecMethodDecl restrictElement(IJml2bConfiguration config, int tag)
		throws PogException {
		if (getStateType().getTag() == tag) {
			return m.getSet(config);
		} else
			return null;
	}

	FormulaWithSpecMethodDecl getModifiedIndexes(IJml2bConfiguration config, int tag, Formula q)
		throws PogException {
		if (getStateType().getTag() == tag) {
			FormulaWithSpecMethodDecl fwp = getRange(config);
			FormulaWithSpecMethodDecl fwp1 = m.getSet(config);
			return new FormulaWithSpecMethodDecl(fwp, fwp1,
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
	private FormulaWithSpecMethodDecl getRange(IJml2bConfiguration config) throws PogException {
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
					FormulaWithSpecMethodDecl fwp1 =this.m.getSet(config);
					FormulaWithSpecMethodDecl fwp2 =((ModifiesLbrack) m).getM().getSet(config);
					FormulaWithSpecMethodDecl fwp3 =getRange(config);
					FormulaWithSpecMethodDecl fwp4 =((ModifiesLbrack) m).getRange(config);
					// m/\m' != {} && sa/\sa' != {} 
					res.add(
						new NormalizedGuardedModifies(
							mo,
							FormulaWithSpecMethodDecl.and(
								new FormulaWithSpecMethodDecl(fwp1, fwp2,
								new BinaryForm(
									INTERSECTION_IS_NOT_EMPTY,
									fwp1.getFormula(),
									fwp2.getFormula())),
									new FormulaWithSpecMethodDecl(fwp3, fwp4,
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
						FormulaWithSpecMethodDecl fwp1 =this.m.getSet(config);
						FormulaWithSpecMethodDecl fwp2 =((ModifiesLbrack) m).getM().getSet(config);
						FormulaWithSpecMethodDecl fwp3 =getRange(config);
						FormulaWithSpecMethodDecl fwp4 =((ModifiesLbrack) m).getRange(config);
						res.add(
							new NormalizedGuardedModifies(
								mo,
								FormulaWithSpecMethodDecl.and(
								                              new FormulaWithSpecMethodDecl(fwp1, fwp2,
									new BinaryForm(
										INTERSECTION_IS_NOT_EMPTY,
										fwp1.getFormula(),
										fwp2.getFormula())),
										new FormulaWithSpecMethodDecl(fwp3, fwp4,
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

//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesDot
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
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.IModifiesField;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubForm;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * This class implements a modifies corresponding to a member field. It declares
 * the member field and the instance on which it is called. This instance is 
 * stored as an expression and as a formula
 * @author L. Burdy
 **/
public class ModifiesDot extends Modifies {

	/**
	 * The instance on which the member field is applied.
	 **/
	private Expression leftE;

	/**
	 * The instance on which the member field is applied.
	 **/
	private transient FormulaWithSpecMethodDecl leftF;

	/**
	 * The member field.
	 **/
	private ModifiesIdent m;

	/*@
	  @ private invariant m != null;
	  @*/

	/**
	 * Constructs an empty modified variable corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesDot(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		leftE = Expression.createE(jf, tree.getFirstChild());
		leftE.parse(tree.getFirstChild());
		m = new ModifiesIdent(jf, tree.getFirstChild().getNextSibling());
	}

	/**
	 * Constructs a modified identifier from an expression and a modified field.
	 * @param pi The parsed item
	 * @param t The type of the field
	 * @param f The expression
	 * @param m The field
	 **/
	/*@
	  @ requires m != null;
	  @*/
	ModifiesDot(ParsedItem pi, Type t, Expression f, ModifiesIdent m) {
		super(pi, t);
		leftE = f;
		this.m = m;
	}

	/**
	 * Constructs a modified identifier from a formula and a modified field.
	 * @param pi The parsed item
	 * @param t The type of the field
	 * @param f The formula
	 * @param m The field
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public ModifiesDot(ParsedItem pi, Type t, FormulaWithSpecMethodDecl f, ModifiesIdent m) {
		super(pi, t);
		leftF = f;
		this.m = m;
	}

	/**
	 * Constructs a modifies corresponding to <code>this.i</code>
	 * @param pi The parsed item corresponding to this modifies
	 * @param i The modifies identifier
	 **/
	ModifiesDot(Field f, Identifier i) {
		super(f, f.getType());
		leftE = new TerminalExp(LITERAL_this, "this");
		m = new ModifiesIdent(f, i);
	}

	public Object clone() {
		return new ModifiesDot(
			this,
			getStateType(),
			leftE == null ? null : (Expression) leftE.clone(),
			(ModifiesIdent) m.clone());
	}

	Vector getParsedItems() {
		Vector res = leftE.getParsedItems();
		res.addAll(m.getParsedItems());
		return res;
	}

	void setParsedItem(ParsedItem pi) {
		leftE.setParsedItem(pi);
		m.setParsedItem(pi);
	}

	/**
	 * Returns the formula corresponding to this modified variable
	 * @return the formula as an application: <code>m(leftF)</code>
	 **/
	FormulaWithSpecMethodDecl getFormula(IJml2bConfiguration config) {
		FormulaWithSpecMethodDecl f = getleftF(config);
		FormulaWithSpecMethodDecl f1 =m.getFormula(config);
		return new FormulaWithSpecMethodDecl(f,f1,
		new BinaryForm(
			IFormToken.B_APPLICATION,
			f1.getFormula(),
			f.getFormula()));
	}

	/**
	 * @return <code>{m(leftF)}</code>
	 **/
	FormulaWithSpecMethodDecl getSet(IJml2bConfiguration config) {
		FormulaWithSpecMethodDecl f = getFormula(config);
		return new FormulaWithSpecMethodDecl(f, new UnaryForm(B_ACCOLADE, f.getFormula()));
	}

	/**
	 * Returns the instance on which the member field is applied.
	 **/
	FormulaWithSpecMethodDecl getleftF(IJml2bConfiguration config) {
		try {
			if (leftF == null)
				return leftF = leftE.exprToForm(config);
			else
				return leftF;
		} catch (PogException pe) {
			throw new jml2b.exceptions.InternalError(pe.toString());

		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}
	}

	/**
	 * @return <code>leftE.m</code>
	 **/
	String toJava(int indent) {
		return (leftE != null ? leftE.toJava(indent) : leftF.getFormula().toLangDefault(indent))
			+ "."
			+ m.toJava(indent);
	}

	LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// Statement left
		LinkInfo lft = leftE.linkStatement(config, f);
		LinkContext l = new LinkContext(f, lft);

		// Statement right
		LinkInfo res = m.linkStatements(config, l);
		setStateType(res.getType());
		return res;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// Statement left
		leftE.typeCheck(config, f);

		// Statement right
		m.typeCheck(config, f);
		return null;

	}

	Modifies instancie() {
		if (m.getIdent().field.isLocal()
			|| m.getIdent().field.getModifiers().isStatic()) {
			return new ModifiesIdent(
				this,
				getStateType(),
				((ModifiesIdent) m).getIdent());
		}
		leftE = (Expression) leftE.instancie();
		return this;
	}

	void instancie(Expression b) {
		leftE = (Expression) leftE.instancie(b);
		leftF = null;
		m.instancie(b);
	}

	/**
	 * @return <code>\forall newM; {left} <<| newM ==  {left} <<| m 
	 *                    ==> s[m <- newM]</code>
	 **/
	Proofs applyMod(IJml2bConfiguration config, IModifiesField me, Proofs s) {
		if (m.getIdent().field.getModifiers().isStatic())
			return m.applyMod(config, me, s);

		ModifiedFieldForm mff = new ModifiedFieldForm(m.getIdent().field, me);

		Proofs res = s.sub(new SubForm(new TerminalForm(m.getIdent()), mff));

		
		FormulaWithSpecMethodDecl fwp = getleftF(config);
		// u = {left} <<| newName ==  {left} <<| m           
		FormulaWithSpecMethodDecl u =
			new FormulaWithSpecMethodDecl(fwp,
			new BinaryForm(
				B_SUBSTRACTION_DOM,
				fwp.getFormula().getNodeType() == ALL_ARRAY_ELEMS ?
					 fwp.getFormula() :
				new UnaryForm(B_ACCOLADE, fwp.getFormula()),
				new BinaryForm(
					B_FUNCTION_EQUALS,
					mff,
					new TerminalForm(m.getIdent()))));

		res.addHyp(u);

		//		if (m.getIdent().field.getType().isBuiltin())
		return res.quantify(
			mff.getNodeText(),
			new BinaryForm(
				IS_MEMBER_FIELD,
				new TTypeForm(
					IFormToken.T_TYPE,
					new Type(m.getIdent().field.getDefiningClass())),
				new TTypeForm(
					IFormToken.T_TYPE,
					m.getIdent().field.getType())));
		//		else 
		//			return res.quantify(
		//				mff,
		//				new BinaryForm(
		//					B_PARTIALFUNCTION,
		//					TerminalForm.REFERENCES,
		//					TerminalForm.REFERENCES));

	}

	boolean is(AField f) {
		return m.is(f);
	}

	/**
	 * @return <code>{leftF}</code> if <code>f</code> is the modified field
	 */
	FormulaWithSpecMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f) {
		if (m.is(f)) {
			FormulaWithSpecMethodDecl fwp = getleftF(config);
			if (fwp.getFormula().getNodeType() == ALL_ARRAY_ELEMS )
				return getleftF(config);
				else
			return new FormulaWithSpecMethodDecl(fwp, new UnaryForm(B_ACCOLADE, fwp.getFormula()));
		
		}
		else
			return null;
	}

	/**
	 * @return <code>null</code>
	 */
	FormulaWithSpecMethodDecl restrictElement(IJml2bConfiguration config, int tag) {
		return null;
	}

	/**
	 * @return <code>null</code>
	 */
	FormulaWithSpecMethodDecl getModifiedIndexes(
		IJml2bConfiguration config,
		int tag,
		Formula q) {
		return null;
	}

	/**
	 * If the depends store ref is a non instanciated field, the instanciated 
	 * dependees are added.
	 * If the depends store ref is an instanciated field, the dependees are 
	 * added with a guard corresponding to
	 * <code>left == left'</code>.
	 * Otherwise no store ref are added.
	 **/
	Vector addDepends(IJml2bConfiguration config, Depends d) {
		Modifies m = d.getAbstractField();
		if (m instanceof ModifiesIdent) {
			if (!((ModifiesIdent) m).getIdent().field.getModifiers().isStatic()
				&& is(((ModifiesIdent) m).getIdent().field)) {
				Vector res = new Vector();
				Enumeration e = d.getConcreteFields().elements();
				while (e.hasMoreElements()) {
					Modifies mo =
						(Modifies) ((Modifies) e.nextElement()).clone();
					mo = mo.instancie();
					mo.instancie(leftE);
					res.add(mo);
				}
				return res;
			}
		} else if (m instanceof ModifiesDot) {
			if (is(((ModifiesDot) m).getM().getIdent().field)) {
				Vector res = new Vector();
				Enumeration e = d.getConcreteFields().elements();
				while (e.hasMoreElements()) {
					Modifies mo =
						(Modifies) ((Modifies) e.nextElement()).clone();
					FormulaWithSpecMethodDecl fwp = getleftF(config);
					FormulaWithSpecMethodDecl fwp1 = ((ModifiesDot) m).getleftF(config);
					res.add(
						new NormalizedGuardedModifies(
							mo,
							new FormulaWithSpecMethodDecl(fwp, fwp1,
							new BinaryForm(
								IFormToken.B_SET_EQUALS,
								fwp.getFormula(),
								fwp1.getFormula()))));
				}
				return res;
			}
		}
		return new Vector();
	}

	Modifies sub(IJml2bConfiguration config, Field a, Field b) {
		FormulaWithSpecMethodDecl newL = getleftF(config).sub(a, b, true);
		return new ModifiesDot(
			this,
			getStateType(),
			newL,
			(ModifiesIdent) m.sub(config, a, b));
	}

	void processIdent() {
		leftE.processIdent();
		m.processIdent();
	}

	AField getField() {
		return m.getField();
	}

	Expression getInstanciation() {
		return leftE;
	}

	boolean isMemberNonInstanciated() {
		return false;
	}

	/**
	 * Returns the member field.
	 * @return <code>m</code>
	 */
	public ModifiesIdent getM() {
		return m;
	}

	static final long serialVersionUID = -3809274145413661524L;

	/* (non-Javadoc)
	 * @see jml2b.structure.jml.Modifies#equals(jml2b.structure.jml.Modifies)
	 */
	public boolean equals(IJml2bConfiguration config, Modifies m) {
		return m instanceof ModifiesDot
			&& ((((ModifiesDot) m).leftE != null && leftE != null)
				? ((ModifiesDot) m).leftE.equals(leftE)
				: ((ModifiesDot) m).getleftF(config).equals(getleftF(config)))
			&& ((ModifiesDot) m).m.equals(config, this.m);
	}
	/**
	 * @return
	 */
	public Expression getLeftE() {
		return leftE;
	}

}

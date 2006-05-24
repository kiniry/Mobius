//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: GuardedModifies
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Collection;
import java.util.HashSet;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IModifiesField;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * This class implements a guarded modifies clause. If the modifies has no 
 * guard, an obvious guard is given.
 * @author L. Burdy
 **/
public class GuardedModifies
	extends ParsedItem
	implements TypeCheckable, JmlDeclParserTokenTypes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The modified store-ref
	 **/
	private Modifies m;

	/**
	 * The guard as an expression
	 **/
	private Expression guardE;

	/*@
	  @ private invariant m != null;
	  @*/

	public Object clone() {
		return new GuardedModifies(
			(Modifies) m.clone(),
			(Expression) guardE.clone());
	}

	/**
	 * Constructs a guarded modifies from a parsed tree
	 * @param jf The current jml file
	 * @param a The AST tree containing the modifies
	 **/
	GuardedModifies(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
		if (a.getType() == LITERAL_if) {
			m = Modifies.create(jf, a.getFirstChild());
			guardE = Expression.createE(jf, a.getFirstChild().getNextSibling());
			guardE.parse(a.getFirstChild().getNextSibling());
		} else {
			m = Modifies.create(jf, a);
			guardE = new TerminalExp(MyToken.BTRUE, "(0=0)");
		}
	}

	/**
	 * Constructs a guarded modifies.
	 * @param m The store-ref
	 * @param e The guard
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public GuardedModifies(Modifies m) {
		this.m = m;
		guardE = new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	GuardedModifies(Modifies m, Expression e) {
		this.m = m;
		guardE = e;
	}

	GuardedModifies(Identifier i, Field f) {
		m = new ModifiesIdent(f, i);
		guardE = new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	GuardedModifies(Field f, Identifier i) {
		if (f.getModifiers() == null || f.getModifiers().isStatic())
			m = new ModifiesIdent(f, i);
		else
			m = new ModifiesDot(f, i);
		guardE = new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	GuardedModifies(Field f) {
		m = new ModifiesLbrack(f);
		guardE = new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	/**
	 * Returns whether a field is modified by this modified variable
	 * @param f The tested field
	 * @return <code>true</code> if the field is modified by this instance, 
	 * <code>false</code> otherwise
	 **/
	boolean is(AField f) {
		return m.is(f);
	}

	/**
	 * Quantifies lemmas and add hypothesis depending on the modified variable.
	 * @param s The proof to quantify.
	 * @return The modified proof.
	 * @throws PogException
	 **/
	Proofs applyMod(IJml2bConfiguration config, IModifiesField me, Proofs s)
		throws PogException {
		return m.applyMod(config, me, s);
	}

	LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		m.linkStatements(config, f);
		guardE.linkStatements(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		m.typeCheck(config, f);
		guardE.typeCheck(config, f);
		return null;
	}

	GuardedModifies subField(IJml2bConfiguration config, Field a, Field b)
		throws PogException {
		return new GuardedModifies(
			getM().sub(config, a, b),
			getGuardE().subField(a, b));
	}

	/**
	 * Instancie the <i>modifies clause</i>.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated <i>modifies clause</i>
	 **/
	NormalizedGuardedModifies instancie(IJml2bConfiguration config)
		throws PogException {
		guardE = (Expression) guardE.instancie();
		try {
			return new NormalizedGuardedModifies(
				m.instancie(),
				guardE,
				guardE.predToForm(config));
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}
	}

	/**
	 * Converts the clause into a string.
	 * @return the original string reconstructed associated with this clause
	 **/
	final String toJava(int indent) {
		if (guardE == null)
			return "";
		else {
			String res = m.toJava(indent);
			if (guardE.getNodeType() == MyToken.BTRUE)
				return res;
			else
				return res + " if " + guardE.toJava(indent + res.length() + 4);

		}
	}

	/**
	 * Collects all the indentifier of the clause to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	void processIdent() {
		m.processIdent();
		guardE.processIdent();
	}

	public void setParsedItem(ParsedItem pi) {
		m.setParsedItem(pi);
		guardE.setParsedItem(pi);
	}

	/**
	 * Returns the state type.
	 * @return the state type
	 */
	Type getStateType() {
		return m.getStateType();
	}

	/**
	 * Returns the guard.
	 * @return <code>guardE</code>
	 */
	Expression getGuardE() {
		return guardE;
	}

	/**
	 * Returns the modified store ref.
	 * @return <code>m</code>
	 */
	public Modifies getM() {
		return m;
	}

	/**
	 * @return
	 */
	public Collection getFields() {
		Collection c = new HashSet();
		c.add(m.getField());
		return c;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(IJml2bConfiguration config, GuardedModifies gm) {
		return guardE.equals(gm.guardE) && m.equals(config, gm.m);
	}

}
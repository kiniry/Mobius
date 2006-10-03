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
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
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

	static final long serialVersionUID = 2677107039781057404L;

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
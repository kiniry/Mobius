/*
 * Created on May 18, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.statement;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 *
 *  @author L. Burdy
 **/
public class StarElemExp extends Expression {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param jf
	 * @param tree
	 */
	public StarElemExp(JmlFile jf, AST tree) {
		super(tree.getType(), "*");
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#subField(jml2b.structure.java.Field, jml2b.structure.java.Field)
	 */
	public Expression subField(Field f, Field newF) {
		return this;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#subResult(java.lang.String)
	 */
	public Expression subResult(String ww) {
		return this;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#processIdent()
	 */
	public void processIdent() {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#equals(jml2b.structure.statement.Expression)
	 */
	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType();
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.jml.JmlExpression#instancie(jml2b.structure.statement.Expression)
	 */
	public JmlExpression instancie(Expression b) {
		return this;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#isConstant()
	 */
	public boolean isConstant() {
		return false;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#old()
	 */
	public void old() {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#toJava(int)
	 */
	public String toJava(int indent) {
		return "*";
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#exprToContextForm(jml2b.IJml2bConfiguration, java.util.Vector, boolean)
	 */
	FormulaWithPureMethodDecl exprToContextForm(IJml2bConfiguration config, Vector methods, boolean pred)
			throws Jml2bException, PogException {
		return null;//new ContextFromPureMethod(new TerminalForm(IFormToken.ALL_ARRAY_ELEMS));
	}

	
	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#isModifiersCompatible(jml2b.structure.java.Modifiers)
	 */
	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) throws LinkException {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.jml.JmlExpression#getParsedItems()
	 */
	public Vector getParsedItems() {
		return new Vector();
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#setParsedItem(jml2b.structure.java.ParsedItem)
	 */
	public void setParsedItem(ParsedItem pi) {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#getFreeVariable(java.util.Set)
	 */
	void getFreeVariable(Set s) {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Statement#parse(antlr.collections.AST)
	 */
	public AST parse(AST tree) throws Jml2bException {
		return null;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Statement#linkStatement(jml2b.IJml2bConfiguration, jml2b.link.LinkContext)
	 */
	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return null;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Statement#getPrecondition(jml2b.IJml2bConfiguration, jml2b.util.ModifiableSet, java.util.Vector, java.util.Vector)
	 */
	public void getPrecondition(IJml2bConfiguration config, ModifiableSet modifies, Vector req, Vector ens)
			throws Jml2bException, PogException {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Statement#collectCalledMethod(java.util.Vector)
	 */
	public void collectCalledMethod(Vector calledMethod) {
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.jml.JmlExpression#instancie()
	 */
	public JmlExpression instancie() {
		return this;
	}

	/* (non-Javadoc)
	 * @see jml2b.link.TypeCheckable#typeCheck(jml2b.IJml2bConfiguration, jml2b.link.LinkContext)
	 */
	public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return Type.getInteger();
	}

}

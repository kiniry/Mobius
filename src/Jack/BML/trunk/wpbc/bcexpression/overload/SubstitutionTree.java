/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.overload;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SubstitutionTree implements Tree {
	Tree left;
	Tree right;

	public SubstitutionTree(Expression expr1, Expression expr2) {
		SubstitutionUnit unit = new SubstitutionUnit(expr1, expr2);
		setLeft(unit);
	}

	public SubstitutionTree(Tree left, Tree right) {
		setLeft(left);
		setRight(right);
	}

	public Tree substitute(Expression e1, Expression e2) {
		if (left != null) {
			left = left.substitute(e1, e2);
		}
		if (right != null) {
			right = right.substitute(e1, e2);
		}
		return this;
	}

	/**
	 * @return
	 */
	public Tree getLeft() {
		return left;
	}

	/**
	 * @return
	 */
	public Tree getRight() {
		return right;
	}

	/**
	 * @param tree
	 */
	public void setLeft(Tree tree) {
		left = tree;
	}

	/**
	 * @param tree
	 */
	public void setRight(Tree tree) {
		right = tree;
	}

	public String toString() {
		String s = left.toString();
		if (right != null) {
			s = s + "   " + right.toString();
		}
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public Tree copy() {

		Tree leftCopy = null;
		if (left != null) {
			leftCopy = left.copy();
		}

		Tree rightCopy = null;
		if (right != null) {
			rightCopy = right.copy();
		}

		SubstitutionTree treeCopy = new SubstitutionTree(leftCopy, rightCopy);
		return treeCopy;
	}

}

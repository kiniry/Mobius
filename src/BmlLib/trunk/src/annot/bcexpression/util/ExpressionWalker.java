package annot.bcexpression.util;

import annot.bcexpression.BCExpression;

/**
 * This class represents an expression iterator.
 * It's subclasses can be used to process expressions using
 * {@link BCExpression#iterate(boolean, ExpressionWalker)}
 * method.
 * 
 * @author tomekb
 */
public abstract class ExpressionWalker {
	
	/**
	 * An integer to store number of performed operations
	 * while expression walking.
	 */
	private int changes = 0;
	
	/**
	 * This method will be called for each node
	 * of the expression's tree.
	 * 
	 * @param parent - parent node, or <b>null</b> at the root,
	 * @param expr - currently processed node (expression).
	 */
	public abstract void iter(BCExpression parent, BCExpression expr);

	/**
	 * @return number of reported operations on expression(s)
	 * 		(since this object creation).
	 */
	public int getChanges() {
		return changes;
	}

	/**
	 * Reports an operation on processed expression.
	 */
	protected void incChanges() {
		this.changes++;
	}
}

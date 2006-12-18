package annot.modifexpression;

import annot.bcexpression.Expression;

public class SingleIndex extends SpecArray {

	public SingleIndex(Expression index ) {
		super(index);
	}
	
	public Expression getIndex() {
		return getSubExpressions()[0];
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "" + getSubExpressions()[0];   
		return s;
	}
	
}

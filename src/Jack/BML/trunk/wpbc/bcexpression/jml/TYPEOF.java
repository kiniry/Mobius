package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class TYPEOF extends JMLExpression {

	public TYPEOF(Expression _left) {
		setLeft(_left );
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
}

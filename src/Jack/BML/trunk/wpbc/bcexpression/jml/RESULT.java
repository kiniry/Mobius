/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;
import java.util.Vector;
import bcexpression.Expression;
import bcexpression.WITH;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import type.BCType;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class RESULT extends JMLExpression {
	private Vector with;
	
	public RESULT() {
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	public Expression substitute(Expression _e1, Expression _e2) {
		if (this.equals(_e1)) {
			return _e2;
		}
		if ((getType() instanceof JavaReferenceType)
				&& (JavaType.subType((JavaType) this.getType(), (JavaType) _e1
						.getType()))) {
			if (with == null) {
				with = new Vector();
			}
			with.add(new WITH(_e1, _e2));
		}
		return this;
	}
}

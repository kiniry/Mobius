/*
 * Created on Feb 2, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bcexpression.overload;

import utils.Util;
import formula.Formula;
import bcexpression.Expression;
import bcexpression.javatype.JavaReferenceType;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class OverloadSubTypeUnit extends OverloadUnit {
	
	public OverloadSubTypeUnit(JavaReferenceType  _expr, Formula _value) {
		super(_expr, _value);
	}

	/* (non-Javadoc)
	 * @see bcexpression.overload.OverloadUnit#getExpressionOverloading(bcexpression.Expression)
	 */
	protected Expression getExpressionOverloading(Expression expr) {
		if (expr == null) {
			Util.dump("Warning : OverloadUnit. getExpressionOverriden :  the argument cannot be null ");
			return null;
		}
		if (! (expr instanceof JavaReferenceType) ) {
			Util.dump("Warning : OverloadUnit. getExpressionOverriden :  the argument cannot be null ");
			return null;
		}
		JavaReferenceType superType = (JavaReferenceType) getObject();  
		JavaReferenceType subType = (JavaReferenceType ) expr;
		if (JavaReferenceType.subType(subType, superType  ) ) {
			return getValue();
		}
		return null;
	}

	
	
}

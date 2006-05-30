/*
 * Created on Feb 2, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.bcexpression.overload;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.formula.Formula;
import bytecode_wp.utils.Util;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class OverloadSubTypeUnit extends OverloadUnit {
	
	public OverloadSubTypeUnit(JavaReferenceType  _expr, Expression _value) {
		super(_expr, _value);
	}

	/* (non-Javadoc)
	 * @see bcexpression.overload.OverloadUnit#getExpressionOverloading(bcexpression.Expression)
	 */
	protected OverloadUnit getExpressionOverloading(Expression expr) {
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
			return this;
		}
		return null;
	}

	
	public Expression copy() {
		Expression refType = getObject().copy();
		Expression valueCopy = getValue().copy();
		OverloadSubTypeUnit unitCopy = new OverloadSubTypeUnit( (JavaReferenceType)refType, valueCopy) ;
		return unitCopy;
	}
	
}

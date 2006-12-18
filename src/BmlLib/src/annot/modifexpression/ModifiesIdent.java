package annot.modifexpression;

import annot.bcclass.BCClass;
import annot.bcexpression.Expression;

public class ModifiesIdent extends ModifiesExpression {
	
	public ModifiesIdent(Expression  ident, BCClass _clazz) {
		super(ident , _clazz);
	}
	
	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
	 */
	public Expression getExpression() {
		return getSubExpressions()[0];
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return null;
	}
	
//	public ModifiesExpression getModifies() {
//		return null;
//	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "modifiesIdent " + getSubExpressions()[0];
	}


	

}

/*
 * Created on Sep 10, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;

import constants.BCConstantClass;
import bcclass.BCConstantPool;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.LocalVariable;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.TYPEOF;

/**
 * 
 * modifies ::= modifiesIdent| modifiesDot | modifiesArray
 * modifiesIdent ::= localvariable | cp_ref_index
 * modifiesDot ::= modifies expression
 * modifiesArray :: = modifies specArray
 * 
 * specArray ::= AllArrayElems(star) | Interval | SingleIndex
 * AllArrayElems ::= *
 * Interval ::= expression expression
 * SingleIndex ::= expression 
 * 
 */

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
//extends Expression
public abstract class ModifiesExpression extends Expression {
	BCConstantPool constantPool;
	protected ModifiesExpression() {
	}
	
	public ModifiesExpression(Expression _e, BCConstantPool _constantPool) {	
		super(_e);
		constantPool = _constantPool;
	}
	
	public ModifiesExpression(Expression _e1, Expression _e2, BCConstantPool _constantPool) {	
		super(_e1, _e2);	
		constantPool = _constantPool;
	}
	public ModifiesExpression getModifies() {
		return (ModifiesExpression) getSubExpressions()[0];
	}
	
	/**
	 * 
	 * @return the constant field reference that is "modified"
	 */
	public Expression getConstantFieldRef() {
		if ( this instanceof ModifiesIdent) {
			return getExpression();
		}
		if ( this instanceof ModifiesDOT ) {
			return getModifies().getConstantFieldRef();
		}
		if (this instanceof ModifiesArray) {
			return getModifies().getConstantFieldRef();
		}
		return null;
		
	}
	
	public Expression getObjectDereferenced() {
		if ( this instanceof ModifiesIdent) {
			return getExpression();
		}
		if ( this instanceof ModifiesDOT ) {
			return getSubExpressions()[1];
		}
		if ( this instanceof ModifiesArray ) {
			ModifiesExpression mod = ((ModifiesArray)this).getModifies();
			Expression objDereferenced = mod.getObjectDereferenced();
			return objDereferenced;
		}
		return null;
	}
	
	
	
	/**
	 * @return Returns the constantPool.
	 */
	public BCConstantPool getConstantPool() {
		return constantPool;
	}
	/**
	 * for an expression a.b.c 
	 * the method determines the class b belongs to.  
	 * @param expr
	 * @param cp
	 * @return
	 */
	public static Expression getClass( Expression expr , BCConstantPool cp ) {
		if (expr instanceof FieldAccess) {
			FieldAccess fAccess = (FieldAccess)expr;
			int index = fAccess.getFieldConstRef().getClassIndex();
			JavaReferenceType javaType = (JavaReferenceType) JavaType.getJavaType( ((BCConstantClass)cp.getConstant(index)).getName() );
			return javaType;
		}
		if ( expr instanceof ArrayAccessExpression  ) {
			ArrayAccessExpression arrAccess = (ArrayAccessExpression)expr;
			JavaReferenceType javaType = 
				(JavaReferenceType) (( JavaArrType)arrAccess.getArray().getType() ).getElementType();
			return javaType;
		}
		if ( expr instanceof LocalVariable) {
			Expression javaType = new TYPEOF( expr); 
				/*(JavaReferenceType) ((LocalVariable)expr).getType();*/
			return javaType;
		}
		return null;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		Expression[] subExprs = getSubExpressions();
		for (int i = 0; i < subExprs.length; i++) {
			subExprs[i] = subExprs[i].substitute(_e1, _e2);
		}
		setSubExpressions(subExprs);
		return this;
	}
	
	public Expression copy() {
		Expression[] expr = getSubExpressions();
		if (this instanceof ModifiesIdent ) {
			Expression exprIdentCopy = expr[0].copy();
			ModifiesIdent modCopy = new ModifiesIdent(exprIdentCopy, constantPool);
			return modCopy;
		}
		if (this instanceof ModifiesDOT ) {
			Expression[] exprCopy = new Expression[expr.length];
			exprCopy[0] = expr[0].copy();
			exprCopy[1] = expr[1].copy();
			ModifiesDOT modCopy = new ModifiesDOT( (ModifiesExpression)exprCopy[0], exprCopy[1] , constantPool);
			return modCopy;
		}
		if (this instanceof ModifiesArray ) {
			Expression[] exprCopy = new Expression[expr.length];
			exprCopy[0] = expr[0].copy();
			exprCopy[1] = expr[1].copy();
			ModifiesArray modCopy = new ModifiesArray( (ModifiesExpression)exprCopy[0], (SpecArray)exprCopy[1] , constantPool);
			return modCopy;
		}
		return null;
	}
	
	//////////////////////////////////
	///////////abstract//////////////////
	public abstract  Expression getPostCondition();
	public abstract  Expression getExpression();

	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//////////////////test////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	public static void main(String[] s) {
		LocalVariable _this = new LocalVariable( 0);	
		/* ModifiesArray mArr = new ModifiesArray( );*/
	} 
}

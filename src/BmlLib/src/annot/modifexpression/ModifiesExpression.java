package annot.modifexpression;

import annot.bcclass.BCClass;
import annot.bcexpression.Expression;

//import jml2b.IJml2bConfiguration;
//import annot.bcclass.BCClass;
//import annot.bcclass.BCConstantPool;
//import bytecode_wp.bcexpression.ArrayAccessExpression;
//import bytecode_wp.bcexpression.BCLocalVariable;
//import bytecode_wp.bcexpression.Expression;
//import bytecode_wp.bcexpression.FieldAccess;
//import bytecode_wp.bcexpression.QuantifiedExpression;
//import bytecode_wp.bcexpression.javatype.JavaArrType;
//import bytecode_wp.bcexpression.javatype.JavaReferenceType;
//import bytecode_wp.bcexpression.javatype.JavaType;
//import annot.constants.ArrayLengthConstant;
//import annot.constants.BCConstantClass;
//import annot.constants.BCConstantFieldRef;
//import annot.constants.MemUsedConstant;

/**
 * 
 * modifies ::= modifiesIdent| modifiesDot | modifiesArray
 * modifiesIdent ::= localvariable | cp_ref_index
 * modifiesDot ::= modifies expression
 * modifiesArray :: = modifies expression specArray
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
	BCClass clazz;
	private Expression type ;
	protected ModifiesExpression() {
		
	}
	
	public ModifiesExpression(Expression _e, BCClass _clazz) {	
		super(_e);
		
	}
	
	public ModifiesExpression(Expression _e1, Expression _e2, BCClass _clazz) {	
		super(_e1, _e2);	
		clazz = _clazz;
//		setType(_clazz.getConstantPool());
	}
	
	public ModifiesExpression getModifies() {
		return (ModifiesExpression) getSubExpressions()[0];
	}
	
//	/**
//	 * 
//	 * @return the expression that is modified
//	 */
//	public Expression getExpressionModifies() {
//		if ( this instanceof ModifiesIdent) {
//			return getExpression();
//		}
//		if ( this instanceof ModifiesDOT ) {
//			return getModifies().getExpressionModifies();
//		}
//		if (this instanceof ModifiesArray) {
//			return getModifies().getExpressionModifies();
//		}
//		return null;
//		
//	}
//	
//	public Expression getObjectDereferenced() {
//		if ( this instanceof ModifiesIdent) {
//			if (getExpression() instanceof BCConstantFieldRef ) {
//				return null; // no object is dereferenced to access the field, i.e. it is a static field
//			}
//			return getExpression();
//		}
//		if ( this instanceof ModifiesDOT ) {
//			return getSubExpressions()[1];
//		}
//		if ( this instanceof ModifiesArray ) {
//			ModifiesExpression mod = ((ModifiesArray)this).getModifies();
//			Expression objDereferenced = mod.getObjectDereferenced();
//			return objDereferenced;
//		}
//		return null;
//	}
//	
//	
//	
//	/**
//	 * @return Returns the constantPool.
//	 */
//	public BCConstantPool getConstantPool() {
//		return clazz.getConstantPool();
//	}
//	/**
//	 * for an expression a.b.c 
//	 * the method determines the class of subexpression b   
//	 * @param expr
//	 * @param cp
//	 * @return
//	 */
//	private void  setType( BCConstantPool cp ) {
//		Expression expr = getExpression();
//		
//		// added recently
//		if (expr instanceof ArrayLengthConstant  ) {
//			type = JavaType.JavaINT;
//			return;
//		}
//		if (expr instanceof MemUsedConstant ) {
//			type = JavaType.JavaINT;
//			return;
//		}
//		// new added recently
//		
//		
//		if (expr instanceof BCConstantFieldRef) {
//			int index = ((BCConstantFieldRef)expr).getClassIndex();
//			JavaReferenceType _type = (JavaReferenceType) JavaType.getJavaType( ((BCConstantClass)cp.getConstant(index)).getName() );
//			type = _type;
//		}
//		if (expr instanceof MemUsedConstant) {
//			type = JavaType.JavaINT;
//		}
//		if (expr instanceof FieldAccess) {
//			FieldAccess fAccess = (FieldAccess)expr;
//			int index = ((BCConstantFieldRef)fAccess.getFieldConstRef()).getClassIndex();
//			JavaReferenceType _type = (JavaReferenceType) JavaType.getJavaType( ((BCConstantClass)cp.getConstant(index)).getName() );
//			type = _type;
//		}
//		if ( expr instanceof ArrayAccessExpression  ) {
//			ArrayAccessExpression arrAccess = (ArrayAccessExpression)expr;
//			JavaType _type = 
//				(JavaType) (( JavaArrType)arrAccess.getArray().getType() ).getElementType();
//			type = _type;
//		}
//		if (expr instanceof QuantifiedExpression) {
//			Expression quantifExpr = ( (QuantifiedExpression)expr).getTheExpressionQuantified();
//			if (quantifExpr instanceof ArrayAccessExpression) {
//				ArrayAccessExpression arrAccess = (ArrayAccessExpression)quantifExpr;
//				Expression arrayAccess = arrAccess.getArray();
//				
//				//JavaType arrType = (JavaType)arrayAccess.getType();
//				//JavaType _type = ( ( JavaArrType)arrType).getElementType();
//				type =(JavaType)arrayAccess.getType();
//			}
//			
//		}
//		if ( expr instanceof BCLocalVariable) {
//			Expression _type = ( (BCLocalVariable)expr).getType(); 
//			type = _type;
//		}
//	}
//	
//	public Expression getType() {
//		return type;
//	}
//	
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		Expression[] subExprs = getSubExpressions();
//		for (int i = 0; i < subExprs.length; i++) {
//			subExprs[i] = subExprs[i].substitute(_e1, _e2);
//		}
//		setSubExpressions(subExprs);
//		return this;
//	}
	
	public Expression copy() {
		Expression[] expr = getSubExpressions();
		if (this instanceof ModifiesIdent ) {
			Expression exprIdentCopy = expr[0].copy();
			ModifiesIdent modCopy = new ModifiesIdent(exprIdentCopy, clazz);
			return modCopy;
		}
		if (this instanceof ModifiesDOT ) {
			Expression[] exprCopy = new Expression[expr.length];
			exprCopy[0] = expr[0].copy();
			exprCopy[1] = expr[1].copy();
			ModifiesDOT modCopy = new ModifiesDOT( (ModifiesExpression)exprCopy[0], exprCopy[1] , clazz);
			return modCopy;
		}
		if (this instanceof ModifiesArray ) {
			Expression[] exprCopy = new Expression[expr.length];
			exprCopy[0] = expr[0].copy();
			exprCopy[1] = expr[1].copy();
			ModifiesArray modCopy = new ModifiesArray( (ModifiesExpression)exprCopy[0], (SpecArray)exprCopy[1] , clazz);
			return modCopy;
		}
		return this;
	}
//	
//	//////////////////////////////////
//	///////////abstract//////////////////
//	public abstract  Expression getPostCondition(IJml2bConfiguration config, int state);
//	
//	/*public abstract Expression getPostConditionWhenCalled(ValueOfConstantAtState constantVar); 
//*/	public abstract  Expression getExpression();
}

/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import java.util.Vector;

import org.apache.bcel.generic.Type;

import bcclass.BCLocalVariable;
import bcexpression.jml.*;
import bcexpression.heap.*;
import bcexpression.type.*;

import constants.BCConstantFieldRef;
import constants.BCConstantInterfaceMethodRef;
import constants.BCConstantMethodReference;




/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ExpressionFactory {
	
	private static ExpressionFactory exprFactory;
	
	private ExpressionFactory() {
	}
	
	public static ExpressionFactory getExpressionFactory() {
		if ( exprFactory != null) {
			return exprFactory;
		}
		exprFactory = new ExpressionFactory();
		return exprFactory;
	} 	

	public  Expression getExpression(Vector _subExprs  , byte _exprType ) {
		Expression expr = null;
		byte type;
		switch (_exprType)  {
			//Arithmetic expression
			case ExpressionConstants.DIV: {
				type = ExpressionConstants.DIV ;
			}
			case ExpressionConstants.MULT:{
				type = ExpressionConstants.MULT ;
			}
			case ExpressionConstants.MINUS:{
				type = ExpressionConstants.MINUS ;
			}
			case ExpressionConstants.PLUS:{
				type = ExpressionConstants.PLUS ;
			}
			case ExpressionConstants.SHL:{
				type = ExpressionConstants.SHL ;
			}
			case ExpressionConstants.SHR: { 
				type = ExpressionConstants.SHR ;
				expr = new ArithmeticExpression((Expression)_subExprs.elementAt(0), (Expression)_subExprs.elementAt(1), type);
			  	return expr;
			}
			
			//CPexpressions
			case ExpressionConstants.ARRAYACCESS: { 
				expr = new ArrayAccessExpression( (Expression)_subExprs.elementAt(0), ((Integer)_subExprs.elementAt(1)).intValue());
				return expr;
			}
						
			case ExpressionConstants.FIELDACCESS: {
				expr = new FieldAccessExpression((BCConstantFieldRef)_subExprs.elementAt(0),(Expression)_subExprs.elementAt(1) );
				return expr;
			}
			case ExpressionConstants.METHOD_CALL: {
				expr = new MethodCallExpression((BCConstantMethodReference)_subExprs.elementAt(0), (Expression)_subExprs.elementAt(1) , (ExpressionList)_subExprs.elementAt(2) );
				return expr;
			}
			case ExpressionConstants.INTERFACE_METHOD_CALL: {
				expr = new StaticMethodCallExpression((BCConstantInterfaceMethodRef)_subExprs.elementAt(0), (Expression)_subExprs.elementAt(1) , (ExpressionList)_subExprs.elementAt(2) );
				return expr;
			}
			//Object access
			case ExpressionConstants.OBJECTACCESS: {
				expr = new ObjectAccess((BCLocalVariable)_subExprs.elementAt(0) );
				return expr;
			}
			case ExpressionConstants.STRING_LITERAL : {
				expr = new StringLiteral(((String)_subExprs.elementAt(0)));
				return expr;
			} 
			case ExpressionConstants.INT_LITERAL : {
				expr = new IntLiteral(((Integer)_subExprs.elementAt(0)).intValue());
				return expr;
			} 
			case ExpressionConstants.NULL : {
				expr = new NULL();
				return expr;
			} 
			case ExpressionConstants.REFERENCE : {
				expr  = new Reference( ((Integer)_subExprs.elementAt(0)).intValue(), (JavaType)_subExprs.elementAt(1)  );
				return expr;
			}
			case ExpressionConstants.VARIABLE: {
				expr  = new Variable( (JavaType)(_subExprs.elementAt(0) ), ((Integer)_subExprs.elementAt(0)).intValue()  );
				return expr;
			}
			//JML expression
			case ExpressionConstants.EXCEPTION_VARIABLE: {
				expr  = new ExceptionVariable( (JavaType)(_subExprs.elementAt(0) ), ((Integer)_subExprs.elementAt(1)).intValue()  );
				return expr;
			}
			case ExpressionConstants.ELEMTYPE : {
				expr = new ELEMTYPE((BCConstantFieldRef)_subExprs.elementAt(0),(Expression)_subExprs.elementAt(1) );
				return expr;
			}
			case ExpressionConstants.OLD: {
				expr = new OLD((Expression)_subExprs.elementAt(0) );
				return expr;
			}
			case ExpressionConstants.TYPEOF: { 
				expr = new TYPEOF((Expression)_subExprs.elementAt(0) );
				return expr;
			}
			case ExpressionConstants.ALL_ARRAY_ELEM : {
				expr = new AllArrayElem((BCConstantFieldRef)_subExprs.elementAt(0) ,(Expression)_subExprs.elementAt(1) );
				return expr;
			}
			
			case ExpressionConstants.ARRAY_ELEM_FROM_TO: {
				expr = new ArrayElemFromTo((BCConstantFieldRef)_subExprs.elementAt(0), (Expression)_subExprs.elementAt(1), ((Integer)_subExprs.elementAt(2) ).intValue(), ((Integer)_subExprs.elementAt(3) ).intValue() ); 
				return expr;
			}
				
			case ExpressionConstants._TYPE: {
				expr = new _Type((JavaType)_subExprs.elementAt(0) ); 
				return expr;
			}
			case ExpressionConstants.RESULT: {
				expr = new RESULT( ); 
				return expr;
			}
			case ExpressionConstants.TYPE: {
				expr = new JML_CONST_TYPE( ); 
				return expr;
			} 
			case ExpressionConstants.JAVA_TYPE: {
				expr = JavaTypeFactory.getJavaTypeFactory().getJavaType((Type)_subExprs.elementAt(0) );
				return expr;
			}
			default:return null;

		}								
		
		
	}
	
	

}

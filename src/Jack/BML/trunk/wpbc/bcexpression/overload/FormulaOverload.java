/*
 * Created on Sep 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.overload;

import utils.Util;
import bcclass.attributes.BCExceptionHandlerTable;
import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.Exsures;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaReferenceType;
import bytecode.BCInstruction;
import bytecode.block.Trace;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class FormulaOverload extends Formula {
	private OverloadList with;
	private Expression expression;

	public FormulaOverload(Trace _trace, Expression _expr, BCInstruction _instr) {
		expression = _expr;
		setSubstitutionTree(_trace, _instr);
		/*Util.dump("FormulaWITH " + this.toString());*/
	}

	public FormulaOverload(OverloadList overload, Expression _expr) {
		expression = _expr;
		with = overload;
		/*Util.dump("FormulaWITH " + this.toString());*/
	}

	/**
	 * ovreloads with the possible exception  types  and the predicate 
	 * that holds after it has been thrown and  
	 * @param _trace
	 */
	private void setSubstitutionTree(Trace _trace, BCInstruction _instr) {
		int position = _instr.getPosition();
		// get the exception handlers for the method
		ExceptionHandler[] excHandlers =
			_trace.getMethod().getExceptionHandlers();
		if (excHandlers != null) {
			for (int i = 0; i < excHandlers.length; i++) {
				JavaObjectType exception = excHandlers[i].getCatchType();
				// searches if this exception handle handles  exception that may be thrown by the instruction 
				Formula excPost =
					_trace.getWpForExcThrownAt(exception, position);
				if (excPost != null) {
					if (with == null) {
						with = new OverloadList(exception, excPost);
						continue;
					}
					with.overload(new OverloadSubTypeUnit(exception, excPost));
				}
			}
		}
		Exsures[] exsures = null;
		if (_trace.getExsTable() != null ) {
			exsures = _trace.getExsTable().getExsures();
		}
		if (( exsures != null ) && (exsures.length > 0 )){
			for (int i = 0; i < exsures.length; i++) {
				if (with == null) {
					with = new OverloadList(exsures[i].getExcType(), exsures[i].getPredicate());
					continue;
				}
				with.overload(	new OverloadSubTypeUnit(exsures[i].getExcType(), exsures[i].getPredicate()));
			}
		}
		
		
		/////////////the rest of the exceptions 
		JavaObjectType[] exceptionsThrown =
			_trace.getMethod().getExceptionsThrown();
		if (exceptionsThrown == null) {
			return;
		}
		for (int i = 0; i < exceptionsThrown.length; i++) {
			// take only the exceptions that  are not caught 
			ExceptionHandler excH =
				_trace.getExceptionHandlerForExceptionThrownAt(
					exceptionsThrown[i],
					position);
			Formula excPost = null;
			// if this exception is not caught then find what is the wp for it.  
			if (excH == null) {
				excPost =  _trace.getMethod().getExsuresForException(exceptionsThrown[i] );
			}
			if (excPost != null) {
				if (with == null) {
					with = new OverloadList(exceptionsThrown[i], excPost);
					continue;
				}
				with.overload(
						new OverloadSubTypeUnit(exceptionsThrown[i], excPost));
			}
		}
		/*ExsuresTable exsTable = _trace.getMethod().getExsures();*/
	}

	public Expression substitute(Expression _e1, Expression _e2) {
		expression = expression.substitute(_e1, _e2);
		with = (OverloadList) with.substitute(_e1, _e2);
		////////////
		// simplification
		Formula t = (Formula)with.getExpressionOverloading(expression);
		if (t != null) {
			return t;
		}
		return this;
	}

	public String toString() {
		String s;
		s = " [  <: " +  expression.toString() + " "+ with.toString() +  " ]";
		return s;
	}
	
	public Expression copy() {
		OverloadList overLoadList =  with.copy();
		Expression exprCopy = expression.copy();
		FormulaOverload copy = new FormulaOverload( overLoadList , exprCopy);
		return copy;
	}

}

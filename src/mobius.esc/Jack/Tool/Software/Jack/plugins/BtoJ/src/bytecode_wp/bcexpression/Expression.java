/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.RESULT;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.vm.Counter;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;

/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public abstract class Expression {
	private Expression[] subExpressions;
	
	public static final Counter COUNTER = Counter.getCounter();

	public static Expression getCOUNTER_PLUS_2() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(2),
			ExpressionConstants.ADD);
	}

	public static Expression getCOUNTER_PLUS_1() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(1),
			ExpressionConstants.ADD);
	}

	public static Expression getCOUNTER_MINUS_1() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(1),
			ExpressionConstants.SUB);
	}

	public static Expression getCOUNTER_MINUS_2() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(2),
			ExpressionConstants.SUB);
	}
	
	
	public static Expression getCOUNTER_MINUS_3() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(3),
			ExpressionConstants.SUB);
	}
	
	public static Expression  getCOUNTER_MINUS_4() {
		return ArithmeticExpression.getArithmeticExpression(
			COUNTER,
			new NumberLiteral(4),
			ExpressionConstants.SUB);
	}
	
	public static final NULL _NULL = NULL.getNULL();

	public static final RESULT _RESULT = RESULT.getResult();
	
	protected Expression() {
	}
	
	public Expression(Expression _subExpr) {
		subExpressions = new Expression[1];
		subExpressions[0] = _subExpr;
	}
	
	public Expression(Expression _subExpr1, Expression _subExpr2) {
		subExpressions = new Expression[2];
		subExpressions[0] = _subExpr1;
		subExpressions[1] = _subExpr2;
	}
	public Expression(Expression[] _subExprs) {
		if (_subExprs != null) {
			subExpressions = _subExprs;
		}
	}
	

	/**
	 * @return Returns the subExpressions.
	 */
	public Expression[] getSubExpressions() {
		return subExpressions;
	}
	/**
	 * @param subExpressions
	 *            The subExpressions to set.
	 */
	public void setSubExpressions(Expression[] subExpressions) {
		this.subExpressions = subExpressions;
	}

	/**
	 * substitute the subexpression (if there are ) equal to _e1 with _e2
	 * 
	 * @param _e1
	 * @param _e2
	 * @return - this object with the substitutions made
	 */
	public abstract Expression substitute(Expression _e1, Expression _e2);
	
	public abstract String toString();

	public boolean equals(Object o) {
		return o.toString().equals(toString());
	}
	
	public int hashCode() {
		return toString().hashCode();
	}
	public  Expression getType() {
		return new TYPEOF( this );
	}
	/**
	 * two expressions are equals if they are from the same type and if they
	 * have the same number of subexpressions and they are equal.
	 * 
	 * @param _expr
	 * @return
	 */
	public boolean equals(Expression _expr) {
		if (_expr == null) {
			return false;
		}
		//if this object and _expr do not have the same type then they are not equal
		if (_expr.getClass() != this.getClass()) {
			return false;
		}
		//		test if the subexpressions are equal
		Expression[] subEofThis = getSubExpressions();
		Expression[] subEofExpr = _expr.getSubExpressions();
		if (((subEofExpr == null) && (subEofThis != null))
			|| ((subEofExpr != null) && (subEofThis == null))) {
			return false;
		}
		//both expressions don't have subexpressions, return true
		if ((subEofExpr == null) && (subEofThis == null)) {
			return true;
		}
		
		if (subEofExpr.length != subEofThis.length ) {
			return false;
		}
		boolean subExprEquals = true;
		if ((subEofExpr != null) && (subEofThis != null)) {
			for (int i = 0; i < subEofThis.length; i++) {
				subExprEquals =
					subExprEquals && subEofThis[i].equals(subEofExpr[i]);
			}
		}
		return subExprEquals;
	}

	public Expression[] copySubExpressions() {
		if (subExpressions == null) {
			return null;
		}
		if (subExpressions.length == 0) {
			return null;
		}
		Expression[] copySubExpr = new Expression[subExpressions.length];
		for (int i = 0; i < copySubExpr.length; i++) {
			copySubExpr[i] = subExpressions[i].copy();
		}
		return copySubExpr;
	}
	/**
	 * renames subexpression of this expression
	 * Renaming must be done in such a way that no capture of variables should be done , i.e. the expr2 must be a fresh variable 
	 * @param expr1
	 * @param expr2
	 * @return
	 */
	public Expression rename(Expression expr1,  Expression expr2 ) {
		if (this.equals( expr1)) {
			return expr2;
		}
		if (subExpressions == null) {
			return this;
		}
		for (int i =0 ; i< subExpressions.length; i++) {
			subExpressions[i] = subExpressions[i].rename(expr1, expr2);
		}
		return this;
	}
	/**
	 * generalises qn expression 
	 * example : generalise(1, var ) ==> returns var 
	 * Used in the modifies expressions when generating proof obligation 
	 * conditions 
	 * 
	 * @param _e1
	 * @param _e2
	 * @return
	 */
	public Expression generalize(Expression _e1 , Expression _e2) {
		if ( this.equals(_e1)) { 
				return _e2;
		}
		if ( subExpressions == null) {
			return this;
		} 
		for (int i = 0; i < subExpressions.length; i++) {
			subExpressions[i] = subExpressions[i].generalize(_e1, _e2);
			setSubExpressions(subExpressions);
		}
		return this;
	}
	public abstract Expression copy();
	
	 
	/**
	 * this method is used to substitute all the expressions that
	 * represent local variables or field references with their values
	 * in the prestate
	 * @return 
	 */
	public Expression valuesInPreState() {
	    Expression[] subExpr = getSubExpressions();
	    
	    if (subExpr == null) {
			return this;
		}
	    if (this instanceof OLD) {
	    	return this;
	    }
	    if (this instanceof BCLocalVariable) {
	        return new OLD(this);
	    }
	    if (this instanceof FieldAccess ) {
	        return new OLD(this);
	    }
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].valuesInPreState();
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	
	/**
	 * substitues  all localvariable l by old(l). This is done over the 
	 * postcondition of the method, as from the client point of view 
	 * changes to the method parameters are not visible as in Java parameters
	 * are passed by value
	 * @return
	 */
	public Expression localVarAtPreState() {
		Expression[] subExpr = getSubExpressions();
		if (this instanceof OLD) {
	    	return this;
	    }
		if (this instanceof BCLocalVariable ) {
			OLD oldlv = new OLD( this);
			return oldlv;
		}
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].localVarAtPreState();
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	/**
	 * @param instrIndex - the instruction at which the value of  array expressions
	 * is "freezeed"
	 * the method converts the expression in an expression that represents
	 * the value of the expression in a state instrIndex
	 */

	public Expression atStateArr(int instrIndex) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].atStateArr( instrIndex);
			
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	/**
	 * @param instrIndex - the instruction at which the value of the expression
	 * is "freezed"
	 * the method converts the expression in an expression that represents
	 * the value of the expression in a state instrIndex
	 */

	public Expression atState(int instrIndex) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].atState( instrIndex);
			
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	/**
	 * this method freezes to the program point specifified by <code>instrIndex</code> only the
	 * expression expr
	 * @param instrIndex
	 * @param expr
	 * @return
	 */
	public Expression atState(int instrIndex, Expression expr) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].atState( instrIndex, expr);
			
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	public Expression atStateOld(int instrIndex) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].atStateOld( instrIndex);
			
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	/**
	 * this method freezes to the program point specifified by <code>instrIndex</code> only the
	 * array expression 
	 * @param instrIndex
	 * @param expr
	 * @return the expression with the corresponding subexpressions freezed
	 */
	public Expression loopModifArrayAtState(int instrIndex, Expression expr ) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].loopModifArrayAtState( instrIndex, expr);
			
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
/*	*//**
	 * this method is used for desugaring the postcondition of a called method 
	 * The method processes the <code>old</code> statements and replaces them with expressions
	 * that are freezed in the state  where the method is called 
	 * @param position - the position of the instruction with which the state is identified 
	 * @return the expression with the modification on old subexpressions if there are such
	 *//*
	public Expression setOldToStateOfInvokation( int position) {
		if ( this instanceof OLD ) {
			Expression exp = getSubExpressions()[0];
			if (exp instanceof FieldAccess) {
				BCConstantFieldRef fieldRef = (BCConstantFieldRef)exp.getSubExpressions()[0];
				exp = exp.atState( position, fieldRef );
				return exp;
			} 
			
		}
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].setOldToStateOfInvokation(  position) ;
		}	
		setSubExpressions(subExprAtState);
		return this;
	}*/
	
	/**
	 * the method removes the old expressions by "extracting" the wrapped objects
	 * into old expressions
	 * 
	 * for example for (old(a + 1)).removeOLD() = a + 1
	 */
	public Expression removeOLD() {
		if (this instanceof OLD) {
			return getSubExpressions()[0];
		}
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		//Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			/*subExprAtState[i] = subExpr[i].removeOLD( );*/
			subExpr[i] = subExpr[i].removeOLD( );
		}	
		//setSubExpressions(subExprAtState);
		return this;
	}
	
	public Expression simplify() {
		return this;
	}
	
	/** 
	 * called from a loop entry point in order to initialize 
	 * the value of this variable
	 * 
	 * @param pos
	 * @return
	 */
	public Expression removeOldLoop(int pos) {
		Expression[] subExpr = getSubExpressions();
		if (subExpr == null) {
			return this;
		}
		Expression[] subExprAtState = new Expression[subExpr.length];
		for ( int i = 0; i < subExpr.length; i++ ) {
			subExprAtState[i] = subExpr[i].removeOldLoop( pos);
		}	
		setSubExpressions(subExprAtState);
		return this;
	}
	
	

    public Formula generateBoolExpressionConditions( ) {
        Expression[] subExpr = getSubExpressions();
        if (subExpr == null) {
            return Predicate0Ar.TRUE;
        }
        Formula condition = Predicate0Ar.TRUE;
        
        //jgc: mmmm... interesting...
       // Expression[] subExprAtState = new Expression[subExpr.length];
        
        for ( int i = 0; i < subExpr.length; i++ ) {
            Formula f = subExpr[i].generateBoolExpressionConditions();
            if ( f != Predicate0Ar.TRUE) {
                condition = Formula.getFormula(condition, f, Connector.AND );
            }
        }
        return condition;
    }
	


    /**
     *  this method returns true if the source type of the expression is true
     *  This is necessary as the type of a boolean expressions on bytecode
     *  level is considered to be integer
     * @return true if the source type of the expression is boolean
     */
    public  boolean isBooleanType() {
    	return false;
    }
}










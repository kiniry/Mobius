package annot.bcexpression;

import java.util.Vector;

import annot.bcclass.BMLConfig;
import annot.bcexpression.jml.RESULT;

public abstract class Expression {
	private Expression[] subExpressions;
	protected byte priority;
	
	public static final byte MAX_PRI = 18; // max priority
	
//	public static final Counter COUNTER = Counter.getCounter();
//
//	public static Expression getCOUNTER_PLUS_2() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(2),
//			ExpressionConstants.ADD);
//	}
//
//	public static Expression getCOUNTER_PLUS_1() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(1),
//			ExpressionConstants.ADD);
//	}
//
//	public static Expression getCOUNTER_MINUS_1() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(1),
//			ExpressionConstants.SUB);
//	}
//
//	public static Expression getCOUNTER_MINUS_2() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(2),
//			ExpressionConstants.SUB);
//	}
//	
//	
//	public static Expression getCOUNTER_MINUS_3() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(3),
//			ExpressionConstants.SUB);
//	}
//	
//	public static Expression  getCOUNTER_MINUS_4() {
//		return ArithmeticExpression.getArithmeticExpression(
//			COUNTER,
//			new NumberLiteral(4),
//			ExpressionConstants.SUB);
//	}
	
	public static final NULL _NULL = NULL.getNULL();

	public static final RESULT _RESULT = RESULT.getResult();
	
	protected Expression() {
		priority = 0;
	}
	
	public Expression(Expression _subExpr) {
		subExpressions = new Expression[1];
		subExpressions[0] = _subExpr;
		priority = 0;
	}

	public Expression(Expression _subExpr1, Expression _subExpr2) {
		subExpressions = new Expression[2];
		subExpressions[0] = _subExpr1;
		subExpressions[1] = _subExpr2;
		priority = 0;
	}

	public Expression(Expression[] _subExprs) {
		if (_subExprs != null) {
			subExpressions = _subExprs;
		}
		priority = 0;
	}
	

	public Expression[] getSubExpressions() {
		return subExpressions;
	}

	public void setSubExpressions(Expression[] subExpressions) {
		this.subExpressions = subExpressions;
	}

//	/**
//	 * substitute the subexpression (if there are ) equal to _e1 with _e2
//	 * 
//	 * @param _e1
//	 * @param _e2
//	 * @return - this object with the substitutions made
//	 */
//	public abstract Expression substitute(Expression _e1, Expression _e2);
//
//	public String toString() {
//		// abstract
//		System.out.println("Unknown expression");
//		return "?";
//	}
//	
//	public abstract String toString();
	
	// abstract
	public String toString() {
		System.err.println("ERROR: called removed method toString().");
		throw new RuntimeException("expression.toString()");
	}
	
	/**
	 * In debug mode (conf.goControlPrint == true),
	 * prints root symbol for this exrpessions.
	 * Should be redefined in some frequently used subclasses.
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return string representation of root of the expression.
	 */
	public String printRoot(BMLConfig conf) {
		return "";
	}
	
	/**
	 * Prints expression in debug (raw) mode
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return string representation of expression
	 */
	public String controlPrint(BMLConfig conf) {
		String str = this.getClass().getName();
		str = str.substring(str.lastIndexOf(".")+1);
		int length = 0;
		if (subExpressions != null)
			length = subExpressions.length;
		conf.incInd();
		if (length > 0)
			str += "(" + printRoot(conf) + ", " + priority;
		for (int i=0; i<length; i++) {
			if (i > 0)
				str += ", ";
			str += "\n" + conf.indent + subExpressions[i].controlPrint(conf);
		}
		if (length > 0)
			str += ")";
		conf.decInd();
		return str;
	}
	
	// position in current line, for line breaking
	// static int line_pos = 0; moved to BMLConfig
	
	/**
	 * Prints expression as a whole attribute
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return string representation of expression
	 */ 
	public String printLine(BMLConfig conf) {
		return printLine(conf, 0);
	}
	
	/**
	 * Prints expression as a whole attribute
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @param usedc - # characters displayed in current line
	 * before this expression
	 * @return string representation of expression
	 */ 
	public String printLine(BMLConfig conf, int usedc) {
		conf.line_pos = usedc;
		conf.root_pri = MAX_PRI;
		conf.incInd();
		conf.expr_depth = 0;
		String str = printCode(conf);
		if (!conf.goSimpleLineBreaking)
			str = conf.pp.breakLines(str, usedc);
		conf.decInd();
		return str;
	}
	
	/**
	 * Adds parenthness to root of the expression.
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return string representation of expression, before
	 * line breaking in the root
	 */
	private String printCode2(BMLConfig conf) {
		int rp = conf.root_pri;
		conf.root_pri = priority;
		String str = "";
		if (conf.goSimpleLineBreaking) {
			str += printCode1(conf);
		} else {
			boolean lvlinc = (rp != priority);
			if (subExpressions == null) {
				lvlinc = true;
			} else if (subExpressions.length == 1)
					lvlinc = false;
			if (lvlinc) {
				conf.expr_depth++;
				str += conf.expr_block_start;
			}
			str += printCode1(conf);
			if (lvlinc) {
				conf.expr_depth--;
				str += conf.expr_block_end;
			}
		}
		if (priority > rp) {
			String str2 = "";
			for (int i=0; i<str.length(); i++) {
				char ch = str.charAt(i);
				if ((ch == ' ') || (ch == '\n') || (ch == '*')) {
					str2 += ch;
				} else {
					str2 += conf.expr_block_start + "(" + str.substring(i, str.length())
						+ ")" + conf.expr_block_end;
					break;
				}
			}
			str = str2;
		}
		conf.root_pri = rp;
		return str;
	}
	
	/**
	 * Prints expression as a string. This method should
	 * be called in attributes and subclasses to get
	 * full string representation.
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return string representation of expression, according
	 * to current configuration and environment (conf)
	 */
	public String printCode(BMLConfig conf) {
		if (conf.goControlPrint) {
			conf.goControlPrint = false;
			String str = printCode(conf);
			conf.goControlPrint = true;
			return str + "\n" + controlPrint(conf);
		} else {
			int old_pos = conf.line_pos;
			String code = printCode2(conf);
			if (code.lastIndexOf("\n") >= 0)
				old_pos = -code.lastIndexOf("\n");
			if (conf.goSimpleLineBreaking)
				if ((code.length() < 20) && (old_pos + code.length() > 80)) {
					conf.line_pos = old_pos = 0;
					code = "\n *      " + printCode2(conf);
				}
			conf.line_pos = old_pos + code.length();
			return code;
		}
	}
	
	/**
	 * This method should be implemented in subclasses to
	 * return it basic string representation (without parenthness
	 * and line-breaking).
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @return debug (raw), ugly representation of expression
	 */
	public String printCode1(BMLConfig conf) {
		System.out.print("in "+this.getClass().getName());
		System.out.println("\tWARNING: replace old method name toString() with printCode1(BMLConf)");
		return controlPrint(conf);
	}
//
//	
//	public  Expression getType() {
//		return new TYPEOF( this );
//	}
//	/**
//	 * two expressions are equals if they are from the same type and if they
//	 * have the same number of subexpressions and they are equal.
//	 * 
//	 * @param _expr
//	 * @return
//	 */
//	public boolean equals(Expression _expr) {
//		if (_expr == null) {
//			return false;
//		}
//		//if this object and _expr do not have the same type then they are not equal
//		if (_expr.getClass() != this.getClass()) {
//			return false;
//		}
//		//		test if the subexpressions are equal
//		Expression[] subEofThis = getSubExpressions();
//		Expression[] subEofExpr = _expr.getSubExpressions();
//		if (((subEofExpr == null) && (subEofThis != null))
//			|| ((subEofExpr != null) && (subEofThis == null))) {
//			return false;
//		}
//		//both expressions don't have subexpressions, return true
//		if ((subEofExpr == null) && (subEofThis == null)) {
//			return true;
//		}
//		
//		if (subEofExpr.length != subEofThis.length ) {
//			return false;
//		}
//		boolean subExprEquals = true;
//		if ((subEofExpr != null) && (subEofThis != null)) {
//			for (int i = 0; i < subEofThis.length; i++) {
//				subExprEquals =
//					subExprEquals && subEofThis[i].equals(subEofExpr[i]);
//			}
//		}
//		return subExprEquals;
//	}
//
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
//	/**
//	 * renames subexpression of this expression
//	 * Renaming must be done in such a way that no capture of variables should be done , i.e. the expr2 must be a fresh variable 
//	 * @param expr1
//	 * @param expr2
//	 * @return
//	 */
//	public Expression rename(Expression expr1,  Expression expr2 ) {
//		if (this.equals( expr1)) {
//			return expr2;
//		}
//		if (subExpressions == null) {
//			return this;
//		}
//		for (int i =0 ; i< subExpressions.length; i++) {
//			subExpressions[i] = subExpressions[i].rename(expr1, expr2);
//		}
//		return this;
//	}
//	/**
//	 * generalises qn expression 
//	 * example : generalise(1, var ) ==> returns var 
//	 * Used in the modifies expressions when generating proof obligation 
//	 * conditions 
//	 * 
//	 * @param _e1
//	 * @param _e2
//	 * @return
//	 */
//	public Expression generalize(Expression _e1 , Expression _e2) {
//		if ( this.equals(_e1)) { 
//				return _e2;
//		}
//		if ( subExpressions == null) {
//			return this;
//		} 
//		for (int i = 0; i < subExpressions.length; i++) {
//			subExpressions[i] = subExpressions[i].generalize(_e1, _e2);
//			setSubExpressions(subExpressions);
//		}
//		return this;
//	}
	public abstract Expression copy();
//	
//	 
//	/**
//	 * this method is used to substitute all the expressions that
//	 * represent local variables or field references with their values
//	 * in the prestate
//	 * @return 
//	 */
//	public Expression valuesInPreState() {
//	    Expression[] subExpr = getSubExpressions();
//	    
//	    if (subExpr == null) {
//			return this;
//		}
//	    if (this instanceof OLD) {
//	    	return this;
//	    }
//	    if (this instanceof BCLocalVariable) {
//	        return new OLD(this);
//	    }
//	    if (this instanceof FieldAccess ) {
//	        return new OLD(this);
//	    }
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].valuesInPreState();
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	
//	
//	/**
//	 * substitues  all localvariable l by old(l). This is done over the 
//	 * postcondition of the method, as from the client point of view 
//	 * changes to the method parameters are not visible as in Java parameters
//	 * are passed by value
//	 * @return
//	 */
//	public Expression localVarAtPreState() {
//		Expression[] subExpr = getSubExpressions();
//		if (this instanceof OLD) {
//	    	return this;
//	    }
//		if (this instanceof BCLocalVariable ) {
//			OLD oldlv = new OLD( this);
//			return oldlv;
//		}
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].localVarAtPreState();
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	
//	
//	
//	/**
//	 * @param instrIndex - the instruction at which the value of the expression
//	 * is instantiated 
//	 * the method converts the expression in an expression that represents
//	 * the value of the expression in a state instrIndex
//	 */
//
//	public Expression atState(int instrIndex) {
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].atState( instrIndex);
//			
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	/**
//	 * this method freezes to the program point specifified by <code>instrIndex</code> only the
//	 * expression expr
//	 * @param instrIndex
//	 * @param expr
//	 * @return
//	 */
//	public Expression atState(int instrIndex, Expression expr) {
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].atState( instrIndex, expr);
//			
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	
//	/**
//	 * this method freezes to the program point specifified by <code>instrIndex</code> only the
//	 * array expression 
//	 * @param instrIndex
//	 * @param expr
//	 * @return the expression with the corresponding subexpressions freezed
//	 */
//	public Expression loopModifArrayAtState(int instrIndex, Expression expr ) {
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].loopModifArrayAtState( instrIndex, expr);
//			
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	
///*	*//**
//	 * this method is used for desugaring the postcondition of a called method 
//	 * The method processes the <code>old</code> statements and replaces them with expressions
//	 * that are freezed in the state  where the method is called 
//	 * @param position - the position of the instruction with which the state is identified 
//	 * @return the expression with the modification on old subexpressions if there are such
//	 *//*
//	public Expression setOldToStateOfInvokation( int position) {
//		if ( this instanceof OLD ) {
//			Expression exp = getSubExpressions()[0];
//			if (exp instanceof FieldAccess) {
//				BCConstantFieldRef fieldRef = (BCConstantFieldRef)exp.getSubExpressions()[0];
//				exp = exp.atState( position, fieldRef );
//				return exp;
//			} 
//			
//		}
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].setOldToStateOfInvokation(  position) ;
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}*/
//	
//	/**
//	 * the method removes the old expressions by "extracting" the wrapped objects
//	 * into old expressions
//	 * 
//	 * for example for (old(a + 1)).removeOLD() = a + 1
//	 */
//	public Expression removeOLD() {
//		if (this instanceof OLD) {
//			return getSubExpressions()[0];
//		}
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		//Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			/*subExprAtState[i] = subExpr[i].removeOLD( );*/
//			subExpr[i] = subExpr[i].removeOLD( );
//		}	
//		//setSubExpressions(subExprAtState);
//		return this;
//	}
//	
//	public Expression simplify() {
//		return this;
//	}
//	
//	/** 
//	 * called from a loop entry point in order to initialize 
//	 * the value of this variable
//	 * 
//	 * @param pos
//	 * @return
//	 */
//	public Expression removeOldLoop(int pos) {
//		Expression[] subExpr = getSubExpressions();
//		if (subExpr == null) {
//			return this;
//		}
//		Expression[] subExprAtState = new Expression[subExpr.length];
//		for ( int i = 0; i < subExpr.length; i++ ) {
//			subExprAtState[i] = subExpr[i].removeOldLoop( pos);
//		}	
//		setSubExpressions(subExprAtState);
//		return this;
//	}
//	
//	
//
//    public Formula generateBoolExpressionConditions( ) {
//        Expression[] subExpr = getSubExpressions();
//        if (subExpr == null) {
//            return Predicate0Ar.TRUE;
//        }
//        Formula condition = Predicate0Ar.TRUE;
//        
//        //jgc: mmmm... interesting...
//       // Expression[] subExprAtState = new Expression[subExpr.length];
//        
//        for ( int i = 0; i < subExpr.length; i++ ) {
//            Formula f = subExpr[i].generateBoolExpressionConditions();
//            if ( f != Predicate0Ar.TRUE) {
//                condition = Formula.getFormula(condition, f, Connector.AND );
//            }
//        }
//        return condition;
//    }
//	
//
//
//    /**
//     *  this method returns true if the source type of the expression is true
//     *  This is necessary as the type of a boolean expressions on bytecode
//     *  level is considered to be integer
//     * @return true if the source type of the expression is boolean
//     */
//    public  boolean isBooleanType() {
//    	return false;
//    }
}

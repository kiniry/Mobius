/*
 * Created on Mar 18, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bcexpression.jml;

import bcexpression.Expression;
import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 * the class models the value for a variable before entering a loop for the first time.
 * This kind of expressions appear only in loop invariants
 * They are not changed when generating the condition for the looop invariant preservation.
 * They are taken into account when the initialization of the invariant is checked : 
 * in this case they are substituted with the expression which is wrapped in 
 * 
 * It is useful when you want to state that the value of variable i becomes never smaller than its value 
 * before starting the loop
 */
public class OLD_LOOP extends JMLExpression {
	private int loopStartPos;

	private JavaType type;

	public OLD_LOOP(Expression _left, int _loopStartPos) {
		super(_left);
		loopStartPos = _loopStartPos;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		Expression type = getSubExpressions()[0].getType();
		return type;
	}

	public Expression rename(Expression expr1,  Expression expr2 ) {
		return this;
	}
	
	 /**
	  * the substitution is realised iff the expression to be substituted - _e1 is equal to this expression 
	  * otherwise the result of the substitution is the same expression. 
 	  */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (equals(_e1)) {
			return _e2;
		}
		return this;
	}



	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpressions = copySubExpressions();
		OLD copy = new OLD(copySubExpressions[0]);
		return copy;
	}
	
	public Expression atState(int state) {
		return this;
	}
	
	/**
	 * 
	 * @param pos
	 * @return
	 */
	public Expression removeOldLoop(int pos) {
		if (pos == loopStartPos) {
			return getSubExpressions()[0];
		}
		return this;
	}
	/**
	 * @return Returns the loopStartPos.
	 */
	public int getLoopStartPos() {
		return loopStartPos;
	}
	
	
	public String toString() {
		Expression expr = (Expression)getSubExpressions()[0];
		String s = "( " +  expr.toString() + "_at_loop_" + loopStartPos + ")";
		return s;
	}
}

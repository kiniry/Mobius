package bytecode_wp.bc.io;


import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;


/**
 * this class is used during the phase of specification loading. 
 * It converts expressions of the form <b>b == !c</b>, where c and b are boolean expessions to the equivalent expression
 * <b>c == 1 ==> b == 0 /\ c == 0 ==> b == 1</b>
 * 
 * It also treats expressions of the form 
 * <b>F connector c</b>  (connector == or, and , implies , etc), where c is a java expression
 * and F a formula . It converts them in 
 * F connector ( c== 1 ==> true   /\ c == 0 ==> false)
 * 
 * 
 * @author mpavlova
 *
 */
public class DesugarTempExpr extends Expression {
	private boolean negated ;
	/**
	 * 
	 * @param cond
	 * @param value
	 */
	public DesugarTempExpr(Expression cond, boolean _negated ) {
		super(cond);
		setNegated(_negated);
	}  
	
	
	public void setNegated(boolean _negated) {
		negated = _negated;
	}
	
	public boolean isNegated() {
		return negated;	
	}
	
	public Formula getFormula() {
		return (Formula)getSubExpressions()[0];	
	}

	public Formula getPositiveCondition () {
		Expression expr = getSubExpressions()[0].copy();
		Expression pos = new NumberLiteral(1);	
		Formula fPos = new Predicate2Ar(expr, pos, PredicateSymbol.EQ );
		return fPos;
	}
	
	public Formula getNegativeCondition () {
		Expression expr = getSubExpressions()[0].copy();
		Expression pos = new NumberLiteral(0);	
		Formula fPos = new Predicate2Ar(expr, pos, PredicateSymbol.EQ );
		return fPos;
	}
	public Expression getPositiveValue() {
		if (isNegated() ) {
			return new NumberLiteral(0);	
		} 
		return new NumberLiteral(1);		
	}
	
	public Expression getNegativeValue() {
		if (isNegated() ) {
			return new NumberLiteral(1);	
		} 
		return new NumberLiteral(0);		
	}
	
	

	
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}

	public String toString() {
		// TODO Auto-generated method stub
		return null;
	}

	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}

}


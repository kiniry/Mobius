/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;
import java.util.Vector;
import type.BCType;
import utils.Util;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ArithmeticExpression extends Expression {
	private byte arithmetic_op;
	
	
	public static ArithmeticExpression getArithmeticExpression(Expression _subExpr1, Expression _subExpr2, byte _op) {
		ArithmeticExpression simplify = simplify(_subExpr1, _subExpr2, _op);
		if ( simplify != null ) {
			return simplify;
		} 
		return new ArithmeticExpression(_subExpr1, _subExpr2,  _op);	
	}
	
	public static ArithmeticExpression getArithmeticExpression(Expression _subExpr1 , byte _op) {
		if (! (_subExpr1 instanceof ArithmeticExpression ) ) {
			new ArithmeticExpression(_subExpr1, _op);	
		}
		ArithmeticExpression simplify = simplify((ArithmeticExpression)_subExpr1,  _op);
		if ( simplify != null ) {
			return simplify;
		} 
		return new ArithmeticExpression(_subExpr1, _op);	
	}
	
	
	public ArithmeticExpression() {
	}
	private  ArithmeticExpression(Expression _subExpr1, Expression _subExpr2,
			byte _arithmetic_op) {

		arithmetic_op = _arithmetic_op;
		setSubExpressions(new Expression[]{_subExpr1, _subExpr2});
	}
	/**
	 * constructor for arithmetic expressions that contain only one
	 * subexpression example : the expression -a is constructed with this
	 * constrcuctor
	 * 
	 * @param _subExpr
	 * @param _arithmetic_op
	 */
	private ArithmeticExpression(Expression _subExpr, byte _arithmetic_op) {
		arithmetic_op = _arithmetic_op;
		setSubExpressions(new Expression[]{_subExpr});
	}
	
	
	/**
	 * simplify arithmetic expressions containing one subexpression _ called
	 * from constructor ArithmeticExpression(Expression _subExpr, byte
	 * _arithmetic_op)
	 * 
	 * @param expr -
	 *            the subexpression of this expression that may be simplified
	 * @param op -
	 *            the op
	 * 
	 * @return a vector of 2 elements : the first element is : either the
	 *         operation of this resulting after the simplification either null
	 *         if no simplification occurred
	 * 
	 * 
	 * expression and the second is : either an array of expressions that are
	 * the subexpressions that are semantically equiv to "op expr" either null
	 * if no simplification occurred
	 */
	protected static ArithmeticExpression simplify(ArithmeticExpression expr, byte op) {
		Vector r = null;
		if (expr instanceof NumberLiteral) {
			int v = ((NumberLiteral) expr).getLiteral();
			//--v ==> v
			if (op == ExpressionConstants.SUB) {
				r = new Vector();
				v = -v;
				//r.add( new Expression[]{new NumberLiteral(v)});
				return new NumberLiteral(v);
			}
			/*
			 * // +-v ==> -v if ((v < 0) && (op == ExpressionConstants.ADD)) {
			 * v = -v; setSubExpressions(new Expression[]{new
			 * NumberLiteral(v)}); arithmetic_op = ExpressionConstants.SUB;
			 * return;
			 */
		}
		// in case this expression is of the form -( a - b) ==> b - a
		if ((expr.getArithmeticOperation() == ExpressionConstants.SUB)
				&& (op == ExpressionConstants.SUB)) {
			r = new Vector();
			Expression[] _aeSubExp = expr.getSubExpressions();
			Expression[] _simplSubExp = new Expression[_aeSubExp.length];
			//invert the array of subexpressions / -( a - b) = b - a
			for (int i = 0; i < _aeSubExp.length; i++) {
				_simplSubExp[i] = _aeSubExp[_aeSubExp.length - i];
			}
			// in case the expression is - - a = a
			if (_aeSubExp.length == 1) {
				expr.setArithmetic_op(ExpressionConstants.NOP);
			}
			//else if there are 2 subexpressions then the op is minus
			if (_aeSubExp.length == 2) {
				expr.setArithmetic_op(ExpressionConstants.SUB);
			}
			expr.setSubExpressions(_simplSubExp);
			return expr;
		}
		//in case nothing is modified
		return null;
	}
	
	/**
	 * @param l1
	 * @param l2
	 * @param op
	 * @return
	 */
	protected static NumberLiteral simplify(NumberLiteral l1, NumberLiteral l2, byte op) {
		NumberLiteral l = eval(l1, l2, op);
		return l;
	}
	
	
	private static ArithmeticExpression _simplifyAdditive(ArithmeticExpression expr1,
			NumberLiteral expr2, byte op) {
		//convert substraction to addition
		if (expr1.getArithmeticOperation() == ExpressionConstants.SUB) {
			expr1.setArithmetic_op(ExpressionConstants.ADD);
			Expression[] sube = expr1.getSubExpressions();
			if (sube[1] instanceof NumberLiteral) {
				sube[1] = new NumberLiteral(-((NumberLiteral) sube[1])
						.getLiteral());
			} else {
				sube[1] = new ArithmeticExpression(sube[1],
						ExpressionConstants.SUB);
			}
		}
		// if the operation is not additive then return
		if (expr1.getArithmeticOperation() != ExpressionConstants.ADD) {
			return null;
		}
		if (expr1 instanceof NumberLiteral) {
			NumberLiteral l = eval((NumberLiteral) expr1, expr2, op);
			return l;
		}

		ArithmeticExpression simpl1 = null;
		ArithmeticExpression simpl2 = null;
		
		if (expr1.getSubExpressions()[0] instanceof ArithmeticExpression) {
			Expression subExpr1Ofexpr1 = expr1.getSubExpressions()[1];
			
			//else try if the left subexpression is an aithlmetic
			// expression to simplify it
			simpl1 = simplify(((ArithmeticExpression) expr1.getSubExpressions()[0]), expr2, op);

		} 
		if (simpl1 != null  ) {
			expr1.setSubExpressions(new Expression[]{simpl1, expr1.getSubExpressions()[1] } );
			return expr1;
		}
		simpl2 = simplify(((ArithmeticExpression) expr1.getSubExpressions()[1]), expr2, op);
		if ( simpl2 != null ) {
			expr1.setSubExpressions(new Expression[]{ expr1.getSubExpressions()[0], simpl2 } );
			return expr1;
		}
		return null;
	}
	
	
	private static ArithmeticExpression _simplifyMultiplicative(
			ArithmeticExpression expr1, NumberLiteral expr2, byte op) {
		if (expr1 instanceof NumberLiteral) {
			NumberLiteral l = eval((NumberLiteral) expr1, expr2, op);
			return l;
		}
		if (expr1.getArithmeticOperation() == ExpressionConstants.MULT
				|| expr1.getArithmeticOperation() == ExpressionConstants.DIV
				|| expr1.getArithmeticOperation() == ExpressionConstants.REM) {

			Expression simpl1 = simplify(expr1.getSubExpressions()[0], expr2,
					op);
			Expression simpl2 = null;
			if (simpl1 != null) {
				expr1.setSubExpressions(new Expression[]{simpl1,
						expr1.getSubExpressions()[1]});
				return expr1;
			} else if (expr1.getSubExpressions().length > 1 ){
				simpl2 = simplify(expr1.getSubExpressions()[1] , expr2, op);
			}
			if (simpl2 != null) {
				expr1.setSubExpressions(new Expression[]{
						expr1.getSubExpressions()[0], simpl2});
				return expr1;
			}
			return null;
		}
		if (expr1.getArithmeticOperation() == ExpressionConstants.ADD
				|| expr1.getArithmeticOperation() == ExpressionConstants.SUB) {
			//arithmetic_op = expr1.getArithmeticOperation();
			ArithmeticExpression simpl1 = simplify(
					expr1.getSubExpressions()[0], expr2, op);
			ArithmeticExpression simpl2 = null;
			if (expr1.getSubExpressions().length > 1 ) {
				simpl2 = simplify(
					expr1.getSubExpressions()[1], expr2, op);
			}
			if ((simpl1 == null) && (simpl2 == null)) {
				return null;
			}
			if ((simpl1 != null) && (simpl2 != null)) { 
				expr1.setSubExpressions(new Expression[]{simpl1, simpl2});
				return expr1;
			}
			//in case that the simplification occurred only in the left part
			// modify the right part as miltiplicative operations are
			// distributive over
			// additives
			if ((simpl1 != null) && (simpl2 == null) && (expr1.getSubExpressions().length > 1 )) {
				simpl2 = new ArithmeticExpression();
				simpl2.setSubExpressions(new Expression[]{
						expr1.getSubExpressions()[1], expr2});
				simpl2.setArithmetic_op(op);
				expr1.setSubExpressions(new Expression[]{simpl1, simpl2});
				return expr1;
			}
			if ((simpl1 == null) && (simpl2 != null)) {
				simpl1 = new ArithmeticExpression();
				simpl1.setSubExpressions(new Expression[]{
						expr1.getSubExpressions()[0], expr2});
				simpl1.setArithmetic_op(op);
				expr1.setSubExpressions(new Expression[]{simpl1, simpl2});
				return expr1;
			}
			
		}
		return null;
	}
	
	public static ArithmeticExpression simplify( Expression expr1, Expression expr2, byte op ) {
		if ((expr1 instanceof NumberLiteral) && (expr2 instanceof NumberLiteral)  ) {
			return simplify( (NumberLiteral)expr1,(NumberLiteral)expr2, op);
		} 
		if ((expr1 instanceof ArithmeticExpression) && (expr2 instanceof NumberLiteral) &&
				( op == ExpressionConstants.MULT || op == ExpressionConstants.DIV || op == ExpressionConstants.REM ) ) {
			return _simplifyMultiplicative( (ArithmeticExpression)expr1,(NumberLiteral)expr2, op);
		}
		
		if ((expr1 instanceof ArithmeticExpression) && (expr2 instanceof NumberLiteral) && 
				( op == ExpressionConstants.ADD || op == ExpressionConstants.SUB ) ) {
			return _simplifyAdditive( (ArithmeticExpression)expr1,(NumberLiteral)expr2, op);
		}
		return null;
	}	
	
	
	
	/*	*//**
				  * simplifies the arithmetic expression
				  * 
				  * example : ( a +1) -2 = a -1
				  * 
				  * @param expr1
				  * @param expr2
				  */
	/*
	 * protected ArithmeticExpression simplify(ArithmeticExpression expr1,
	 * NumberLiteral expr2, byte op) { boolean simplified = false; //if the
	 * operation is additive one then simplification can be made if // the
	 * expr1 is also an additive one // as + and - are not distributive over
	 * multiplicative operations if (op == ExpressionConstants.ADD || op ==
	 * ExpressionConstants.SUB) { if (expr1.getArithmeticOperation() ==
	 * ExpressionConstants.SUB) {
	 * expr1.setArithmetic_op(ExpressionConstants.ADD); Expression[] sube =
	 * expr1.getSubExpressions(); if (sube[1] instanceof NumberLiteral) {
	 * sube[1] = new NumberLiteral(-((NumberLiteral) sube[1]) .getLiteral()); }
	 * else { sube[1] = new ArithmeticExpression(sube[1],
	 * ExpressionConstants.SUB); } } if (expr1.getArithmeticOperation() ==
	 * ExpressionConstants.ADD) { simplified = _simplifyAdditive(expr1, expr2,
	 * op); } } if (op == ExpressionConstants.MULT || op ==
	 * ExpressionConstants.DIV || op == ExpressionConstants.REM) { simplified =
	 * _simplifyMultiplicative(expr1, expr2, op ); } return simplified;
	 */
	/**
	 * evals what is the value of two number literals
	 * 
	 * @param v1
	 * @param v2
	 * @param b
	 * @return
	 */
	public static NumberLiteral eval(NumberLiteral l1, NumberLiteral l2, byte op) {
		int v1 = l1.getLiteral();
		int v2 = l2.getLiteral();
		int r = 0;
		if (op == ExpressionConstants.ADD) {
			r = v1 + v2;
		}
		if (op == ExpressionConstants.DIV) {
			r = v1 / v2;
		}
		if (op == ExpressionConstants.MULT) {
			r = v1 * v2;
		}
		if (op == ExpressionConstants.SUB) {
			r = v1 - v2;
		}
		if (op == ExpressionConstants.REM) {
			r = v1 % v2;
		}
		return new NumberLiteral(r);
	}
	/**
	 * @return the code of the operation of this expression for example the
	 *         code of plus, minus
	 */
	public byte getArithmeticOperation() {
		return arithmetic_op;
	}
	public BCType getType() {
		return null;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		if (!(_expr instanceof ArithmeticExpression)) {
			return false;
		}
		ArithmeticExpression arithExpr = (ArithmeticExpression) _expr;
		if (arithExpr.getArithmeticOperation() != getArithmeticOperation()) {
			return false;
		}
		//test if the subexpressions are equal
		boolean subExprEquals = true;
		Expression[] subEofThis = getSubExpressions();
		Expression[] subEofExpr = arithExpr.getSubExpressions();
		for (int i = 0; i < subEofThis.length; i++) {
			subExprEquals = subExprEquals
					&& subEofThis[i].equals(subEofExpr[i]);
		}
		return subExprEquals;
	}
	
	
	/**
	 * substitute the subexpression (if there are ) equal to _e1 with _e2
	 * 
	 * @param _e1
	 * @param _e2
	 * @return - this object with the substitutions made
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (this.equals(_e1)) {
			return _e2;
		}
		Expression[] subExpr = getSubExpressions();
		for (int i = 0; i < subExpr.length; i++) {
			subExpr[i] = subExpr[i].substitute(_e1, _e2);
		}
		return this;
	}
	
	
	/**
	 * @param arithmetic_op
	 *            The arithmetic_op to set.
	 */
	public void setArithmetic_op(byte arithmetic_op) {
		this.arithmetic_op = arithmetic_op;
	}
	public String toString() {
		String op = "";
		if (arithmetic_op == ExpressionConstants.ADD) {
			op = " + ";
		}
		if (arithmetic_op == ExpressionConstants.SUB) {
			op = " - ";
		}
		if (arithmetic_op == ExpressionConstants.MULT) {
			op = " * ";
		}
		if (arithmetic_op == ExpressionConstants.DIV) {
			op = " / ";
		}
		if (arithmetic_op == ExpressionConstants.REM) {
			op = " % ";
		}
		Expression[] subExpr = getSubExpressions();
		if (getSubExpressions().length == 1) {
			return "(" + op + subExpr[0] + ")";
		} else {
			return "(" + subExpr[0] + op + subExpr[1] + ")";
		}
	}
	
	
	public static void main(String[] args) {
		NumberLiteral _1 = new NumberLiteral(1);
		NumberLiteral _2 = new NumberLiteral(2);
		ArithmeticExpression _counter_minus_1 = getArithmeticExpression(_1,
				Expression.COUNTER, ExpressionConstants.SUB);
		
		ArithmeticExpression.dump(" 1 - counter : " + _counter_minus_1.toString());
		

		ArithmeticExpression _2_minus_counter = getArithmeticExpression(
				_counter_minus_1, new NumberLiteral(3), ExpressionConstants.SUB);
		
		ArithmeticExpression.dump("-2 + (- counter) :  " + _2_minus_counter.toString());
		
		ArithmeticExpression a1= getArithmeticExpression(
				_2_minus_counter, new NumberLiteral(5), ExpressionConstants.MULT);
		ArithmeticExpression.dump("-10 + ( (-counter)*5) :  " +  a1.toString());
		
		ArithmeticExpression a2 = getArithmeticExpression(
				a1, new NumberLiteral(2), ExpressionConstants.MULT);
		ArithmeticExpression.dump("-20 + ( (-counter)*10) :  " +  a2.toString());
		
		ArithmeticExpression a3 = getArithmeticExpression(
				a2, new NumberLiteral(2), ExpressionConstants.DIV);
		ArithmeticExpression.dump("-20 + ( (-counter)*10) :  " +  a2.toString());
		
		
		/*
		 * ArithmeticExpression twicecounter_minus_4_plus1 = new
		 * ArithmeticExpression( twicecounter_minus_4, new NumberLiteral(1),
		 * ExpressionConstants.ADD);
		 * ArithmeticExpression.dump(twicecounter_minus_4_plus1.toString());
		 * ArithmeticExpression twicecounter_minus_4_plus1_plus2 = new
		 * ArithmeticExpression( twicecounter_minus_4_plus1, new
		 * NumberLiteral(2), ExpressionConstants.ADD);
		 * ArithmeticExpression.dump(twicecounter_minus_4_plus1_plus2.toString());
		 * ArithmeticExpression twicecounter_minus_4_plus1_plus2_plus1 = new
		 * ArithmeticExpression( twicecounter_minus_4_plus1_plus2, new
		 * NumberLiteral(1), ExpressionConstants.ADD);
		 * ArithmeticExpression.dump(twicecounter_minus_4_plus1_plus2_plus1
		 */
	}
	public static void dump(String str) {
		if (Util.DUMP) {
			System.out.println(str);
		}
	}
}

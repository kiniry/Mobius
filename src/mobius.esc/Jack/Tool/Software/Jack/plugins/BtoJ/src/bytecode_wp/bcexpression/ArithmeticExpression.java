/*
 * Created on Mar 4, 2004
 *
 */
package bytecode_wp.bcexpression;

import jack.util.Logger;

import java.util.Vector;

import bytecode_wp.bcexpression.javatype.JavaBasicType;
import bytecode_wp.utils.Util;

/**
 * @author mpavlova
 * 
 */
public class ArithmeticExpression extends Expression {
	private byte arithmetic_op;

	/**
	 * outside from this class only this method may be called in order to get a
	 * new arithmetic expressions. It simplifies the _subExpr1 and _subExpr2 and
	 * may not create a new instance of ArithmeticExpression class form them and
	 * the operation op. If there is possible to execute an evaluation step then
	 * it does it
	 * 
	 * @param _subExpr1
	 * @param _subExpr2
	 * @param _op
	 * @return
	 */
	public static Expression getArithmeticExpression(Expression _subExpr1,
			Expression _subExpr2, byte _op) {
		Expression simplify = simplify(_subExpr1, _subExpr2, _op);
		if (simplify != null) {
			return simplify;
		}
		return new ArithmeticExpression(_subExpr1, _subExpr2, _op);
	}

	/**
	 * outside from this class only this method may be called in order to get a
	 * new arithmetic expressions. It simplifies the _subExpr1 and may not
	 * create a new instance of ArithmeticExpression class
	 * 
	 * @param _subExpr1
	 * @param _op
	 * @return
	 */
	public static ArithmeticExpression getArithmeticExpression(
			Expression _subExpr1, byte _op) {
		ArithmeticExpression e = null;
		if (!(_subExpr1 instanceof ArithmeticExpression)) {
			e = new ArithmeticExpression(_subExpr1, _op);
			
		} else {
			e = simplify((ArithmeticExpression) _subExpr1, _op);
			if ( e == null) {
				e = new ArithmeticExpression(_subExpr1, _op);
			} 
		}
		return e;
	    /*if (simplify != null) {
			return simplify;
		} else if ( e )
		
		
		return e; //new ArithmeticExpression(e, _op);
*/	}

	public ArithmeticExpression() {
	}

	public ArithmeticExpression(Expression _subExpr1, Expression _subExpr2,
			byte _arithmetic_op) {
		super(new Expression[] { _subExpr1, _subExpr2 });
		arithmetic_op = _arithmetic_op;
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
		setSubExpressions(new Expression[] { _subExpr });
	}

	/**
	 * simplify arithmetic expressions containing one subexpression _ called
	 * from constructor ArithmeticExpression(Expression _subExpr, byte
	 * _arithmetic_op)
	 * 
	 * @param expr -
	 *            the subexpression of this expression that may be simplified
	 * @param op -
	 *            the arithmetic operation to be performed
	 * 
	 * @return null if no simplifications may be done. Returns the simplified
	 *         object if a simplification is possible
	 * 
	 */
	protected static ArithmeticExpression simplify(ArithmeticExpression expr,
			byte op) {
		Vector r = null;
		if (expr instanceof NumberLiteral) {
			int v = ((NumberLiteral) expr).getLiteral();
			// --v ==> v
			if (op == ExpressionConstants.SUB) {
				r = new Vector();
				v = -v;
				// r.add( new Expression[]{new NumberLiteral(v)});
				return new NumberLiteral(v);
			}
			/*
			 * // +-v ==> -v if ((v < 0) && (op == ExpressionConstants.ADD)) { v =
			 * -v; setSubExpressions(new Expression[]{new NumberLiteral(v)});
			 * arithmetic_op = ExpressionConstants.SUB; return;
			 */
		}
		// in case this expression is of the form -( a - b) ==> b - a
		if ((expr.getArithmeticOperation() == ExpressionConstants.SUB)
				&& (op == ExpressionConstants.SUB)) {
			r = new Vector();
			Expression[] _aeSubExp = expr.getSubExpressions();
			Expression[] _simplSubExp = new Expression[_aeSubExp.length];
			// invert the array of subexpressions / -( a - b) = b - a
			for (int i = 0; i < _aeSubExp.length; i++) {
				_simplSubExp[i] = _aeSubExp[_aeSubExp.length - i];
			}
			// in case the expression is - - a = a
			if (_aeSubExp.length == 1) {
				expr.setArithmetic_op(ExpressionConstants.NOP);
			}
			// else if there are 2 subexpressions then the op is minus
			if (_aeSubExp.length == 2) {
				expr.setArithmetic_op(ExpressionConstants.SUB);
			}
			expr.setSubExpressions(_simplSubExp);
			return expr;
		}
		// in case nothing is modified
		return null;
	}

	/**
	 * @param l1
	 * @param l2
	 * @param op
	 * @return
	 */
	protected static NumberLiteral simplify(NumberLiteral l1, NumberLiteral l2,
			byte op) {
		NumberLiteral l = eval(l1, l2, op);
		return l;
	}

	/**
	 * makes simplifications on additive operations - <b>+</b> or <b>-</b>
	 * 
	 * @param expr1
	 * @param expr2
	 * @param op
	 *            where op is <b>+</b> or <b>-</b>
	 * @return
	 */
	private static Expression _simplifyAdditive(ArithmeticExpression expr1,
			NumberLiteral expr2, byte op) {

		
		// convert substraction to addition
		if (expr2.getLiteral() == 0) {
			return expr1;
		}
		if (expr1.getArithmeticOperation() == ExpressionConstants.SUB) {
			expr1.setArithmetic_op(ExpressionConstants.ADD);
			Expression[] sube = expr1.getSubExpressions();
			if (sube.length < 2) {
				return getArithmeticExpression( sube[0], expr2, op );
			}
			// changes the expression expr1 = a -b intp expr1 = a + (-b)
			if (sube.length == 2) {
				if (sube[1] instanceof NumberLiteral) {
					sube[1] = new NumberLiteral(-((NumberLiteral) sube[1])
							.getLiteral());
				} else {
					sube[1] = new ArithmeticExpression(sube[1],
							ExpressionConstants.SUB);
				}

			}
		}
		// if the operation is not additive then return
		if (expr1.getArithmeticOperation() != ExpressionConstants.ADD ) {
			return null;
		}
		if (expr1 instanceof NumberLiteral) {
			NumberLiteral l = eval((NumberLiteral) expr1, expr2, op);
			return l;
		}

		Expression simpl1 = null;
		Expression simpl2 = null;

		if (expr1.getSubExpressions()[0] instanceof ArithmeticExpression) {
			Expression subExpr1Ofexpr1 = expr1.getSubExpressions()[1];

			// else try if the left subexpression is an aithlmetic
			// expression to simplify it
			simpl1 = simplify(
					( expr1.getSubExpressions()[0]),
					expr2, op);

		}
		// start :new code
		if ((simpl1 != null) && (simpl1 instanceof NumberLiteral)
				&& (((NumberLiteral) simpl1).getLiteral() == 0)) {
			return expr1.getSubExpressions()[1];
		}
		// end : new code

		if (simpl1 != null) {
			expr1.setSubExpressions(new Expression[] { simpl1,
					expr1.getSubExpressions()[1] });
			return expr1;
		}
		simpl2 = simplify(
				(expr1.getSubExpressions()[1]), expr2,
				op);
		// start :new code
		if ((simpl2 != null) && (simpl2 instanceof NumberLiteral)
				&& (((NumberLiteral) simpl2).getLiteral() == 0)) {
			return expr1.getSubExpressions()[0];
		}
		// end : new code
		if (simpl2 != null) {
			expr1.setSubExpressions(new Expression[] {
					expr1.getSubExpressions()[0], simpl2 });
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
				expr1.setSubExpressions(new Expression[] { simpl1,
						expr1.getSubExpressions()[1] });
				return expr1;
			} else if (expr1.getSubExpressions().length > 1) {
				simpl2 = simplify(expr1.getSubExpressions()[1], expr2, op);
			}
			if (simpl2 != null) {
				expr1.setSubExpressions(new Expression[] {
						expr1.getSubExpressions()[0], simpl2 });
				return expr1;
			}
			return null;
		}
		if (expr1.getArithmeticOperation() == ExpressionConstants.ADD
				|| expr1.getArithmeticOperation() == ExpressionConstants.SUB) {
			// arithmetic_op = expr1.getArithmeticOperation();
			Expression simpl1 = simplify(expr1.getSubExpressions()[0], expr2,
					op);
			Expression simpl2 = null;
			if (expr1.getSubExpressions().length > 1) {
				simpl2 = simplify(expr1.getSubExpressions()[1], expr2, op);
			}
			if ((simpl1 == null) && (simpl2 == null)) {
				return null;
			}
			if ((simpl1 != null) && (simpl2 != null)) {
				expr1.setSubExpressions(new Expression[] { simpl1, simpl2 });
				return expr1;
			}
			// in case that the simplification occurred only in the left part
			// modify the right part as miltiplicative operations are
			// distributive over
			// additives
			if ((simpl1 != null) && (simpl2 == null)
					&& (expr1.getSubExpressions().length > 1)) {
				simpl2 = new ArithmeticExpression();
				simpl2.setSubExpressions(new Expression[] {
						expr1.getSubExpressions()[1], expr2 });
				((ArithmeticExpression) simpl2).setArithmetic_op(op);
				expr1.setSubExpressions(new Expression[] { simpl1, simpl2 });
				return expr1;
			}
			if ((simpl1 == null) && (simpl2 != null)) {
				simpl1 = new ArithmeticExpression();
				simpl1.setSubExpressions(new Expression[] {
						expr1.getSubExpressions()[0], expr2 });
				((ArithmeticExpression) simpl1).setArithmetic_op(op);
				expr1.setSubExpressions(new Expression[] { simpl1, simpl2 });
				return expr1;
			}

		}
		return null;
	}

	public static Expression simplify(Expression expr1, Expression expr2,
			byte op) {
		if ((expr1 instanceof NumberLiteral)
				&& (expr2 instanceof NumberLiteral)) {
			return simplify((NumberLiteral) expr1, (NumberLiteral) expr2, op);
		}
		if ((op == ExpressionConstants.MULT || op == ExpressionConstants.DIV || op == ExpressionConstants.REM)) {
			if ((expr1 instanceof ArithmeticExpression)
					&& (expr2 instanceof NumberLiteral)) {
				return _simplifyMultiplicative((ArithmeticExpression) expr1,
						(NumberLiteral) expr2, op);
			}
		}
		if ((op == ExpressionConstants.ADD || op == ExpressionConstants.SUB)) {
			if ((expr1 instanceof ArithmeticExpression)
					&& (expr2 instanceof NumberLiteral)) {
				return _simplifyAdditive((ArithmeticExpression) expr1,
						(NumberLiteral) expr2, op);
			}
			if (expr2 instanceof NumberLiteral) {
				int val2 = ((NumberLiteral) expr2).getLiteral();
				if (val2 == 0) {
					return expr1;
				}
			}
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
	 * @return the code of the operation of this expression for example the code
	 *         of plus, minus
	 */
	public byte getArithmeticOperation() {
		return arithmetic_op;
	}

	public Expression getType() {
		return JavaBasicType.JavaINT;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#setType()
	 * 
	 * public void setType() { // TODO Auto-generated method stub }
	 */

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		if (!equals) {
			return false;
		}
		ArithmeticExpression arithExpr = (ArithmeticExpression) _expr;
		if (arithmetic_op == arithExpr.getArithmeticOperation()) {
			return true;
		}
		return false;

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
			return _e2.copy();
		}
		Expression[] subExpr = getSubExpressions();
		Expression[] subExpr1 = new Expression[subExpr.length];
		for (int i = 0; i < subExpr.length; i++) {
			// Util.dump(subExpr[i].toString());
			subExpr1[i] = subExpr[i].substitute(_e1, _e2);
		}

		setSubExpressions(subExpr1);
		// if this expression can be evaluated then evaluate it
		Expression simplify = null;
		if ((getSubExpressions() != null) && (getSubExpressions().length == 2)) {
			simplify = getArithmeticExpression(getSubExpressions()[0],
					getSubExpressions()[1], arithmetic_op);

		} else {
			simplify = getArithmeticExpression(getSubExpressions()[0],
					arithmetic_op);
		}
		if (simplify != null) {
			return simplify;
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
		if (arithmetic_op == ExpressionConstants.NEG) {
			op = " - ";
		}
		Expression[] subExpr = getSubExpressions();
		if (getSubExpressions().length == 1) {
			return op + subExpr[0];
		} else {
			return subExpr[0] + op + subExpr[1];
		}
	}

	/**
	 * for test purposes
	 * 
	 * @param args
	 */
	public static void main(String[] args) {
		// (counter + 1)[counter<-(counter + 1)]
		ArithmeticExpression count_plus_1 = new ArithmeticExpression(
				Expression.COUNTER, new NumberLiteral(1),
				ExpressionConstants.ADD);
		Expression subst = count_plus_1.substitute(Expression.COUNTER,
				new ArithmeticExpression(Expression.COUNTER, new NumberLiteral(
						1), ExpressionConstants.ADD));
		Util.dump(" count _plus_1" + count_plus_1.toString());
		Util.dump("substitute " + subst.toString());
	}

	public static void main1(String[] args) {
		NumberLiteral _1 = new NumberLiteral(1);
		NumberLiteral _2 = new NumberLiteral(2);
		ArithmeticExpression _counter_minus_1 = (ArithmeticExpression) getArithmeticExpression(
				_1, Expression.COUNTER, ExpressionConstants.SUB);

		ArithmeticExpression.dump(" 1 - counter : "
				+ _counter_minus_1.toString());

		ArithmeticExpression _2_minus_counter = (ArithmeticExpression) getArithmeticExpression(
				_counter_minus_1, new NumberLiteral(3), ExpressionConstants.SUB);

		ArithmeticExpression.dump("-2 + (- counter) :  "
				+ _2_minus_counter.toString());

		ArithmeticExpression a1 = (ArithmeticExpression) getArithmeticExpression(
				_2_minus_counter, new NumberLiteral(5),
				ExpressionConstants.MULT);
		ArithmeticExpression.dump("-10 + ( (-counter)*5) :  " + a1.toString());

		ArithmeticExpression a2 = (ArithmeticExpression) getArithmeticExpression(
				a1, new NumberLiteral(2), ExpressionConstants.MULT);
		ArithmeticExpression.dump("-20 + ( (-counter)*10) :  " + a2.toString());

		ArithmeticExpression a3 = (ArithmeticExpression) getArithmeticExpression(
				a2, new NumberLiteral(2), ExpressionConstants.DIV);
		ArithmeticExpression.dump("-20 + ( (-counter)*10) :  " + a2.toString());

		/*
		 * for debugging purposes only ArithmeticExpression
		 * twicecounter_minus_4_plus1 = new ArithmeticExpression(
		 * twicecounter_minus_4, new NumberLiteral(1), ExpressionConstants.ADD);
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
			Logger.get().println(str);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpr = copySubExpressions();
		ArithmeticExpression copy = null;
		if (copySubExpr.length == 1) {
			copy = new ArithmeticExpression(copySubExpr[0], arithmetic_op);
		} else {
			copy = new ArithmeticExpression(copySubExpr[0], copySubExpr[1],
					arithmetic_op);
		}
		return copy;
	}

}

/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.formula;

import java.util.Vector;

import bytecode_wp.bc.io.DesugarNegBoolExpr;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Formula extends Expression {

	private byte connector;

	public static final boolean SIMPLIFY = true;

	protected Formula() {
	}

	protected Formula(Expression _f) {
		super(_f);
	}

	protected Formula(Expression[] _f, byte _conn) {
		super(_f);
		setConnector(_conn);
	}

	protected Formula(Expression _f, byte _conn) {
		super(_f);
		setConnector(_conn);
	}

	protected Formula(Expression _left, Expression _right, byte _conn) {
		super(_left, _right);
		setConnector(_conn);
	}

	// constructor used by subclass Predicate
	protected Formula(Expression _left, Expression _right) {
		super(_left, _right);
	}

	public static Formula getFormula(Formula f1, Quantificator[] quantifiers) {
		if (f1 == Predicate0Ar.TRUE) {
			return f1;
		}
		if (f1 == Predicate0Ar.FALSE) {
			return f1;
		}
		QuantifiedFormula f = null;
		/*
		 * if (f1 instanceof QuantifiedFormula) { f = (QuantifiedFormula) f1; if
		 * (quantifiers == null) { return f1; } for (int i = 0; i <
		 * quantifiers.length; i++) { f.addQuantificator(quantifiers[i]); }
		 * return f; }
		 */
		f = new QuantifiedFormula(f1, quantifiers);
		return f;
	}

	public static Formula getFormula(Formula f1, Quantificator quantifier) {
		if (f1 == Predicate0Ar.TRUE) {
			return f1;
		}
		if (f1 == Predicate0Ar.FALSE) {
			return f1;
		}
		QuantifiedFormula f = null;
		/*
		 * if (f1 instanceof QuantifiedFormula) { f = (QuantifiedFormula) f1;
		 * f.addQuantificator(quantifier); return f; }
		 */
		f = new QuantifiedFormula(f1, quantifier);
		return f;
	}

	public static Formula getFormula(Formula _f1, byte _connector) {
		if (_connector == Connector.NOT) {
			Formula f = simplifyNOT(_f1);
			if (f == null) {
				f = new Formula(_f1, Connector.NOT);
				return f;
			}
		}
		return null;
	}

	/**
	 * NB: A==> B ==> C ==> D will be treated as A ==> (B ==> ( C ==> D))
	 * 
	 * @param _f
	 * @param _connector
	 * @return
	 */
	public static Formula getFormula(Vector _f, byte _connector) {
		Formula f;
		if (_f.size() == 1) {
			f = getFormula((Formula) _f.elementAt(0), _connector);
		}
		f = Predicate0Ar.TRUE;
		for (int i = 0; i < _f.size(); i++) {
			f = getFormula(f, (Formula) _f.elementAt(i), _connector);
		}
		return f;
	}

	/*
	 * public Formula[] getSubformulas() { Formula[] subformulas =
	 * (Formula[])getSubexpressions(); return subformulas; }
	 */

	/**
	 * generates from _f1, _f2, connector a simplfied formula
	 */
	public static Formula getFormula(Formula _f1, Formula _f2, byte _connector) {
		Formula f = null;
		if (_connector == Connector.IMPLIES) {
			f = simplifyIMPLIES(_f1, _f2);
			if (f != null) {
				return f;
			}
			f = new Formula(_f1, _f2, Connector.IMPLIES);
			return f;

		} else if (_connector == Connector.AND) {
			f = simplifyAND(_f1, _f2);
			if (f != null) {
				return f;
			}
			f = new Formula(_f1, _f2, Connector.AND);
			return f;

		} else if (_connector == Connector.OR) {
			f = simplifyOR(_f1, _f2);
			if (f != null) {
				return f;
			}
			f = new Formula(_f1, _f2, Connector.OR);
			return f;

		} else if (_connector == Connector.EQUIV) {
			f = new Formula(_f1, _f2, Connector.EQUIV);
			return f;
		}
		return null;
	}

	private static Formula simplifyNOT(Formula _f1) {
		if (!SIMPLIFY) {
			return null;
		}
		if (_f1 == Predicate0Ar.TRUE) {
			return Predicate0Ar.FALSE;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.TRUE;
		}
		return null;

	}

	public static Formula simplifyAND(Formula _f1, Formula _f2) {
		if (!SIMPLIFY) {
			return null;
		}
		if (_f1.equals(_f2)) {
			_f2 = null;
			return _f1;
		}
		if (_f1 == Predicate0Ar.TRUE) {
			_f1 = null;
			return _f2;
		}
		if (_f2 == Predicate0Ar.TRUE) {
			_f2 = null;
			return _f1;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.FALSE;
		}
		if (_f2 == Predicate0Ar.FALSE) {
			return Predicate0Ar.FALSE;
		}

		if (isContradiction(_f1, _f2)) {

			return Predicate0Ar.FALSE;
		}
		return null;
	}

	/**
	 * the method detects if the two arguments are contradicting formulasof the
	 * form : a== b and !(a == b)
	 * 
	 * @param _f1
	 * @param _f2
	 * @return true if the arguments are contradictory formulas otherwise
	 *         returns false
	 */
	public static boolean isContradiction(Formula _f1, Formula _f2) {
		if (_f1.getConnector() == Connector.NOT) {
			Formula ff = _f1;
			_f1 = _f2;
			_f2 = ff;
		}

		if (_f2.getConnector() == Connector.NOT) {
			Formula negated = (Formula) _f2.getSubExpressions()[0];
			if (negated.equals(_f1)) {
				return true;
			}
		}
		if ((_f1.getConnector() == Connector.AND)
				&& (_f2.getConnector() != Connector.AND)) {
			Formula ff = _f1;
			_f1 = _f2;
			_f2 = ff;
		}
		if ((_f2 instanceof Formula) && (_f2.getConnector() == Connector.AND)) {
			for (int i = 0; i < _f2.getSubExpressions().length; i++) {
				boolean isContradiction = isContradiction(_f1, (Formula) _f2
						.getSubExpressions()[i]);
				if (isContradiction) {
					return true;
				}
			}
		}
		return false;
	}

	private static Formula simplifyOR(Formula _f1, Formula _f2) {

		if (!SIMPLIFY) {
			return null;
		}
		if (_f1 == Predicate0Ar.TRUE) {
			return Predicate0Ar.TRUE;
		}
		if (_f2 == Predicate0Ar.TRUE) {
			return Predicate0Ar.TRUE;
		}
		if ((_f1 == Predicate0Ar.FALSE) && (_f2 == Predicate0Ar.FALSE)) {
			return Predicate0Ar.FALSE;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return _f2;
		}
		if (_f2 == Predicate0Ar.FALSE) {
			return _f1;
		}
		return null;

	}

	private static Formula simplifyIMPLIES(Formula _f1, Formula _f2) {
		if (!SIMPLIFY) {
			return null;
		}
		if (_f2 == Predicate0Ar.TRUE) {
			return Predicate0Ar.TRUE;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.TRUE;
		}
		if ((_f1 == Predicate0Ar.TRUE) && (_f2 == Predicate0Ar.FALSE)) {
			return Predicate0Ar.FALSE;
		}
		/*
		 * if ( _f2 == Predicate0Ar.FALSE ) { return getFormula( _f1,
		 * Connector.NOT); }
		 */
		if (_f1 == Predicate0Ar.TRUE) {
			return _f2;
		}

		// if _f2 is an implication and has the same hypothesis (syntaxic equals
		// ) as _f1
		// 
		if (_f2.getConnector() == Connector.IMPLIES) {
			Formula hyp = (Formula) _f2.getSubExpressions()[0];
			if (hyp.equals(_f1)) {
				_f1 = null;
				return _f2;
			}
			// if the formula _f2 is an implies then the hypothesis of
			// _f2 are conjuncted with _f1
			hyp = Formula.getFormula(_f1, hyp, Connector.AND);
			// the conjunction implies the same as _f2
			_f2 = Formula.getFormula(hyp, (Formula) _f2.getSubExpressions()[1],
					Connector.IMPLIES);
			return _f2;
		}
		return null;
	}

	/**
	 * @return Returns the connector.
	 */
	public byte getConnector() {
		return connector;
	}

	/**
	 * @param connector
	 *            The connector to set.
	 */
	private void setConnector(byte connector) {
		this.connector = connector;
	}

	/**
	 * substitute the expression _e in this formula by the expression _v
	 * 
	 * @param _e
	 * @param _v
	 * @return this[ _e <- _v]
	 */
	public Expression substitute(Expression _e, Expression _v) {
		// Util.dump(toString());
		Expression[] subformulas = (Expression[]) getSubExpressions();
		for (int i = 0; i < subformulas.length; i++) {
			subformulas[i] = subformulas[i].substitute(_e, _v);
		}
		Expression simplify = simplify();
		return simplify;
	}

	public Expression simplify() {
		Expression[] subFromulas = getSubExpressions();
		Formula f = null;
		if (connector == Connector.NOT) {
			subFromulas[0] = ((Formula) subFromulas[0]).simplify();
			f = simplifyNOT((Formula) subFromulas[0]);
		} else if (connector == Connector.IMPLIES) {
			subFromulas[0] = ((Formula) subFromulas[0]).simplify();
			subFromulas[1] = ((Formula) subFromulas[1]).simplify();
			f = simplifyIMPLIES((Formula) subFromulas[0],
					(Formula) subFromulas[1]);
		} else if (connector == Connector.AND) {
			subFromulas[0] = ((Formula) subFromulas[0]).simplify();
			subFromulas[1] = ((Formula) subFromulas[1]).simplify();
			f = simplifyAND((Formula) subFromulas[0], (Formula) subFromulas[1]);
		} else if (connector == Connector.OR) {
			subFromulas[0] = ((Formula) subFromulas[0]).simplify();
			subFromulas[1] = ((Formula) subFromulas[1]).simplify();
			f = simplifyOR((Formula) subFromulas[0], (Formula) subFromulas[1]);
		} else if (connector == Connector.EQUIV) {
			subFromulas[0] = ((Formula) subFromulas[0]).simplify();
			subFromulas[1] = ((Formula) subFromulas[1]).simplify();
			f = simplifyEQUIV((Formula) subFromulas[0],
					(Formula) subFromulas[1]);
		}

		if (f != null) {
			return f;
		}
		return this;
	}

	private Formula simplifyEQUIV(Formula formula, Formula formula2) {
		if (formula == Predicate0Ar.TRUE) {
			return formula2;
		}
		if (formula2 == Predicate0Ar.TRUE) {
			return formula;
		}

		if (formula.equals(formula2)) {
			return Predicate0Ar.TRUE;
		}
		return null;
	}

	public Expression copy() {
		Expression[] subformulas = getSubExpressions();

		Expression[] _subformulas = new Formula[subformulas.length];
		for (int i = 0; i < subformulas.length; i++) {
			_subformulas[i] = (Formula) subformulas[i].copy();
		}
		Formula _copy = new Formula((Formula[]) _subformulas, connector);
		return _copy;
	}

	public String toString() {
		String con = "";
		if (connector == Connector.AND) {
			con = " && ";
		}
		if (connector == Connector.OR) {
			con = " || ";
		}
		if (connector == Connector.IMPLIES) {
			con = " ==> ";
		}
		if (connector == Connector.NOT) {
			con = " ! ";
		}
		if (connector == Connector.EQUIV) {
			con = " <==> ";
		}
		Expression[] subformulas = getSubExpressions();
		if (subformulas.length == 1) {
			return "(" + con + subformulas[0] + ")";
		} else {
			String s = "" + subformulas[0];
			for (int i = 1; i < subformulas.length; i++) {
				s = s + con + subformulas[i];
			}

			return s;
		}
	}

	/**
	 * the renaming actually here is a special substition which affects also
	 * variables under quantifiction rename expr1 by expr2 Renaming must be done
	 * in such a way that no capture of variables should be done , i.e. the
	 * expr2 must be a fresh variable
	 * 
	 * @param expr1
	 * @param expr2
	 * @return
	 */
	public Expression rename(Expression expr1, Expression expr2) {
		Expression[] subformulas = getSubExpressions();
		if (subformulas == null) {
			return this;
		}
		for (int i = 0; i < subformulas.length; i++) {
			subformulas[i] = ((Formula) subformulas[i]).rename(expr1, expr2);
		}
		return this;
	}

	/**
	 * 2 formulas are equals if they are of the same type and the subformulas
	 * they have are equals
	 * 
	 * @param formula
	 * @return
	 */
	public boolean equals(Formula formula) {
		if (formula.getClass() != this.getClass()) {
			return false;
		}
		if (formula.getConnector() != getConnector()) {
			return false;
		}
		Expression[] subformulas = getSubExpressions();
		Expression[] _subformulas = formula.getSubExpressions();
		if (((subformulas == null) && (_subformulas == null))) {
			return true;
		}
		if (subformulas.length != _subformulas.length) {
			return true;
		}
		boolean subFormulasEq;
		for (int i = 0; i < subformulas.length; i++) {
			Expression f = subformulas[i];
			Expression _f = _subformulas[i];
			subFormulasEq = f.equals(_f);
			if (!(subFormulasEq)) {
				return false;
			}
		}
		return true;
		/*
		 * boolean eq = super.equals(formula); if ( ! eq ) { return false; } if
		 * (formula.getConnector() != getConnector()) { return false; } return
		 * true;
		 */
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JavaType.JavaBOOLEAN;
	}

	public Vector elimConj() {
		Vector v = new Vector();
		if (getConnector() != Connector.AND) {
			v.add(this);
			return v;
		}
		Expression[] f = getSubExpressions();
		for (int i = 0; i < f.length; i++) {
			Vector vsub = ((Formula) f[i]).elimConj();
			v.addAll(vsub);
		}
		return v;
	}

	public static Formula getFormula(Expression f1, Expression f2, byte connector) {
		if (!  ( f1 instanceof Formula ) ) {
			if ( f1 instanceof DesugarNegBoolExpr) {
				f1 =  ( (DesugarNegBoolExpr)f1).getNegativeCondition();
			} else {
				f1 = new Predicate2Ar( f1 , new NumberLiteral(1), PredicateSymbol.EQ );
			}
		
		}	
		
		if (!  ( f2 instanceof Formula ) ) {
			if ( f2 instanceof DesugarNegBoolExpr) {
				f2 =  ( (DesugarNegBoolExpr)f2).getNegativeCondition();
			} else {
				f2 = new Predicate2Ar( f2 , new NumberLiteral(1), PredicateSymbol.EQ );
			}
		
		}	
		Formula formula = Formula.getFormula((Formula)f1, (Formula)f2, connector);
			return formula;
		
	}}
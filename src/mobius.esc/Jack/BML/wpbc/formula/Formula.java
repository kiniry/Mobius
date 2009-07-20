/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import utils.Util;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcexpression.Expression;
import bcexpression.NULL;
import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Formula extends Expression {

	/* private Formula[] subformulas; */

	private byte connector;

	protected Formula() {
	}

	protected Formula(Formula _f) {
		super(_f);
	}

	private Formula(Formula[] _f, byte _conn) {
		super(_f);
		setConnector(_conn);
	}

	private Formula(Formula _f, byte _conn) {
		super(_f);
		setConnector(_conn);
	}

	private Formula(Formula _left, Formula _right, byte _conn) {
		super(_left, _right);
		setConnector(_conn);

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
	public static Formula getFormula(Formula[] _f, byte _connector) {
		Formula f;
		if (_f.length == 1) {
			f = getFormula(_f[0], _connector);
		}
		f = _f[0];
		for (int i = 1; i < _f.length; i++) {
			f = getFormula(f, _f[i], _connector);
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

		}
		return null;
	}

	private static Formula simplifyNOT(Formula _f1) {
		if (_f1 == Predicate0Ar.TRUE) {
			return Predicate0Ar.FALSE;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.TRUE;
		}
		return null;

	}

	private static Formula simplifyAND(Formula _f1, Formula _f2) {
		if (_f1.equals(_f2)) {
			_f2 = null;
			return _f1;
		}
		if (_f1 == Predicate0Ar.TRUE) {
			_f1 = null;
			return _f2;
		}
		if (_f2 == Predicate0Ar.TRUE) {
			return _f1;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.FALSE;
		}
		if (_f2 == Predicate0Ar.FALSE) {
			return Predicate0Ar.FALSE;
		}
	    // a hypothese matches with <code>a == null</code> and another with
	    //     <code>!a == null</code>
		if ( ( _f1 instanceof Predicate2Ar )
				&& ( _f2 instanceof Formula  )
				&& ( _f2.getConnector() == Connector.NOT)
				&& (_f2.getSubExpressions()[0] instanceof Predicate2Ar )
			 ) { 				
				Predicate2Ar negated = (Predicate2Ar)_f2.getSubExpressions()[0];
				if ( negated.equals(_f1 )) {
					return Predicate0Ar.FALSE;
				}
			 /*&& ( ( (Predicate2Ar)_f1).getConnector() == PredicateSymbol.EQ ) 
			 && (( (Predicate2Ar)_f2).getConnector() == PredicateSymbol.EQ )  )*/ 
			 
		}
		
		return null;
	}

	private static Formula simplifyOR(Formula _f1, Formula _f2) {
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
		if (_f2 == Predicate0Ar.TRUE) {
			return Predicate0Ar.TRUE;
		}
		if (_f1 == Predicate0Ar.FALSE) {
			return Predicate0Ar.TRUE;
		}
		if ((_f1 == Predicate0Ar.TRUE) && (_f2 == Predicate0Ar.FALSE)) {
			return Predicate0Ar.FALSE;
		}
		/*if ( _f2 == Predicate0Ar.FALSE ) {
			return getFormula( _f1, Connector.NOT);
		}*/
		if (_f1 == Predicate0Ar.TRUE) {
			return _f2;
		}
	
		// if _f2 is an implication and has the same hypothesis (syntaxic equals ) as _f1 
		// 
		if (_f2.getConnector() == Connector.IMPLIES) {
			Formula hyp = (Formula) _f2.getSubExpressions()[0];
			if (hyp.equals(_f1)) {
				_f1 = null;
				return _f2;
			}
			// if the  formula _f2 is an implies then  the hypothesis of 
			// _f2 are conjuncted with _f1 
			hyp = Formula.getFormula( _f1, hyp, Connector.AND );
			// the conjunction implies  the same as  _f2
			_f2 = Formula.getFormula( hyp, (Formula)_f2.getSubExpressions()[1], Connector.IMPLIES );
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
		//Util.dump(toString());
		Expression[] subformulas = (Expression[]) getSubExpressions();
		for (int i = 0; i < subformulas.length; i++) {
			subformulas[i] = subformulas[i].substitute(_e, _v);
		}
		Expression simplify = simplify();
		return simplify;
	}

	protected Expression simplify() {
		Expression[] subFromulas = getSubExpressions();
		Formula f = null;
		if (connector == Connector.NOT) {
			f = simplifyNOT((Formula) subFromulas[0]);
		} else if (connector == Connector.IMPLIES) {
			f = simplifyIMPLIES((Formula) subFromulas[0],
					(Formula) subFromulas[1]);
		} else if (connector == Connector.AND) {
			f = simplifyAND((Formula) subFromulas[0], (Formula) subFromulas[1]);
		} else if (connector == Connector.OR) {
			f = simplifyOR((Formula) subFromulas[0], (Formula) subFromulas[1]);
		}
		if (f != null) {
			return f;
		}
		return this;
	}

	public Expression copy() {
		Expression[] subformulas = getSubExpressions();

		/*
		 * if ( !(subformulas instanceof Formula[]) ) { Util.dump("ill formula :
		 * subexpression is not formula but: its type is " +
		 * subformulas[0].getClass() + " its super type is " +
		 * subformulas[0].getClass().getSuperclass() ) ; Util.dump("ill formula :
		 * subexpression is not formula but: its type is " +
		 * subformulas[1].getClass() + " its super type is " +
		 * subformulas[1].getClass().getSuperclass() ) ; Util.dump("ill formula :
		 * subexpressions are not formulas: " + subformulas[0].getClass() + " " +
		 * subformulas[1].getClass() ); }
		 */
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
		Expression[] subformulas = getSubExpressions();
		if (subformulas.length == 1) {
			return "(" + con + subformulas[0] + ")";
		} else {
			String s = "" + subformulas[0];
			for (int i = 1; i < subformulas.length; i++) {
				s = s + con + subformulas[i];
			}
			s = "( " + s + " )";
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
			Formula f = (Formula) subformulas[i];
			Formula _f = (Formula) _subformulas[i];
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
}
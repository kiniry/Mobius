/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import type.BCType;
import formula.atomic.Predicate;

import bcexpression.Expression;
import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Formula  {

	private Formula[] subformulas;

	private byte connector;

	protected Formula() {
	}

	private Formula(Formula[] _f, byte _conn) {
		setConnector(_conn);
		subformulas = _f;
	}

	private Formula(Formula _f, byte _conn) {
		setConnector(_conn);
		subformulas = new Formula[1];
		subformulas[0] = _f;
	}

	private Formula(Formula _left, Formula _right, byte _conn) {
		setConnector(_conn);
		subformulas = new Formula[2];
		subformulas[0] = _left;
		subformulas[1] = _right;
	}

	public static Formula getFormula(Formula f1, Quantificator[] quantifiers) {
		if (f1 == Predicate.TRUE) {
			return f1;
		}
		if (f1 == Predicate.FALSE) {
			return f1;
		}
		QuantifiedFormula f = null;
		if (f1 instanceof QuantifiedFormula) {
			f = (QuantifiedFormula) f1;
			if (quantifiers == null) {
				return f1;
			}
			for (int i = 0; i < quantifiers.length; i++) {
				f.addQuantificator(quantifiers[i]);
			}
			return f;
		}
		f = new QuantifiedFormula(f1, quantifiers);
		return f;
	}

	public static Formula getFormula(Formula f1, Quantificator quantifier) {
		if (f1 == Predicate.TRUE) {
			return f1;
		}
		if (f1 == Predicate.FALSE) {
			return f1;
		}
		QuantifiedFormula f = null;
		if (f1 instanceof QuantifiedFormula) {
			f = (QuantifiedFormula) f1;
			f.addQuantificator(quantifier);
			return f;
		}
		f = new QuantifiedFormula(f1, quantifier);
		return f;
	}

	public static Formula getFormula(Formula _f1, byte _connector) {
		if (_connector == Connector.NOT) {
			Formula f = simplifyNOT(_f1);
			return f;
		}
		return null;
	}

	/**
	 * NB: A==> B ==> C ==> D will be treated as A ==> (B ==> ( C ==> D))
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

	public Formula[] getSubformulas() {
		return subformulas;
	}

	public static Formula getFormula(
		Formula _f1,
		Formula _f2,
		byte _connector) {
		Formula f = null;
		if (_connector == Connector.IMPLIES) {
			f = simplifyIMPLIES(_f1, _f2);
			return f;
		} else if (_connector == Connector.AND) {
			f = simplifyAND(_f1, _f2);
			return f;
		} else if (_connector == Connector.OR) {
			f = simplifyOR(_f1, _f2);
			return f;
		}
		return null;
	}

	private static Formula simplifyNOT(Formula _f1) {
		if (_f1 == Predicate.TRUE) {
			return Predicate.FALSE;
		}
		if (_f1 == Predicate.FALSE) {
			return Predicate.TRUE;
		}
		Formula f = new Formula(_f1, Connector.NOT);
		return f;
	}

	private static Formula simplifyAND(Formula _f1, Formula _f2) {
		if (_f1.equals(_f2)) {
			return _f1;
		}

		if (_f1 == Predicate.TRUE) {
			return _f2;
		}
		if (_f2 == Predicate.TRUE) {
			return _f1;
		}
		if (_f1 == Predicate.FALSE) {
			return Predicate.FALSE;
		}
		if (_f2 == Predicate.FALSE) {
			return Predicate.FALSE;
		}
		Formula f = new Formula(_f1, _f2, Connector.AND);
		return f;
	}

	private static Formula simplifyOR(Formula _f1, Formula _f2) {
		if (_f1 == Predicate.TRUE) {
			return Predicate.TRUE;
		}
		if (_f2 == Predicate.TRUE) {
			return Predicate.TRUE;
		}
		if ((_f1 == Predicate.FALSE) && (_f2 == Predicate.FALSE)) {
			return Predicate.FALSE;
		}
		if (_f1 == Predicate.FALSE) {
			return _f2;
		}
		if (_f2 == Predicate.FALSE) {
			return _f1;
		}
		Formula f = new Formula(_f1, _f2, Connector.OR);
		return f;
	}

	private static Formula simplifyIMPLIES(Formula _f1, Formula _f2) {
		if (_f2 == Predicate.TRUE) {
			return Predicate.TRUE;
		}
		if (_f1 == Predicate.FALSE) {
			return Predicate.TRUE;
		}
		if ((_f1 == Predicate.TRUE) && (_f2 == Predicate.FALSE)) {
			return Predicate.FALSE;
		}
		if (_f1 == Predicate.TRUE) {
			return _f2;
		}
		if (_f2.getConnector() == Connector.IMPLIES) {
			Formula hyp = _f2.getSubformulas()[0];
			if (hyp.equals(_f1)) {
				return _f2;
			}
		}
		Formula f = new Formula(_f1, _f2, Connector.IMPLIES);
		return f;
	}

	/**
	 * @return Returns the connector.
	 */
	public byte getConnector() {
		return connector;
	}
	/**
	 * @param connector The connector to set.
	 */
	private void setConnector(byte connector) {
		this.connector = connector;
	}

	/**
	 * substitute the expression _e in this formula by the expression _v
	 * @param _e
	 * @param _v
	 * @return  this[ _e <- _v]
	 */
	public Formula substitute(Expression _e, Expression _v) {
		//Util.dump(toString());

		for (int i = 0; i < subformulas.length; i++) {
			subformulas[i] = subformulas[i].substitute(_e, _v);
		}
		return this;
	}

	public Formula copy() {
		Formula[] _subformulas = new Formula[subformulas.length];
		for (int i = 0; i < subformulas.length; i++) {
			_subformulas[i] = subformulas[i].copy();
		}
		Formula _copy = new Formula(_subformulas, connector);
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

		if (subformulas.length == 1) {
			return "(" + con + subformulas[0] + ")";
		} else {
			String s = "" + subformulas[0];
			for (int i = 1; i < subformulas.length; i++) {
				s = s + con + subformulas[i] ;
			}
			s = "( "+  s + " )";
			return s;
		}
	}

	/**
	 * the renaming actually here is a special substition which affects also  variables under quantifiction 
	 * rename expr1 by expr2
	 * Renaming must be done in such a way that no capture of variables should be done , i.e. the expr2 must be a fresh variable 
	 * @param expr1
	 * @param expr2
	 * @return
	 */
	public Formula rename(Expression expr1, Expression expr2) {
		if (subformulas == null) {
			return this;
		}
		for (int i = 0; i < subformulas.length; i++) {
			subformulas[i] = subformulas[i].rename(expr1, expr2);
		}
		return this;
	}

	/**
	 * 2 formulas are equals if they are of the same type and the subformulas they have are equals
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
		if ( ( subformulas == null ) && (formula.getSubformulas() == null) ) {
			return true;
		}
		boolean subFormulasEq = subformulas[0].equals( formula.getSubformulas()[0]);
		subFormulasEq = subFormulasEq && subformulas[1].equals(formula.getSubformulas()[1]);
		return subFormulasEq;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		return JavaType.JavaBOOLEAN;
	}
}

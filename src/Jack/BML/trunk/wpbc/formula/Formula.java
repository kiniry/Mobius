/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import formula.atomic.Predicate;
import utils.Util;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Formula {

	private Formula[] subformulas;

	private byte connector;

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
		if ( _f.length == 1) {
			f = getFormula( _f[0], _connector);
		}
		f = _f[0];
		for (int i = 1; i < _f.length; i++) {
			f = getFormula(f, _f[i], _connector);
		}
		return f;
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
		if (_f1 == Predicate._TRUE) {
			return Predicate._FALSE;
		}
		if (_f1 == Predicate._FALSE) {
			return Predicate._TRUE;
		}
		Formula f = new Formula(_f1, Connector.NOT);
		return f;
	}

	private static Formula simplifyAND(Formula _f1, Formula _f2) {
		if ((_f1 == Predicate._TRUE) && (_f2 == Predicate._TRUE)) {
			return Predicate._TRUE;
		}
		if (_f1 == Predicate._TRUE ) {
			return _f2;
		}
		if (_f2 == Predicate._TRUE ) {
			return _f1;
		}
		if (_f1 == Predicate._FALSE) {
			return Predicate._FALSE;
		}
		if (_f2 == Predicate._FALSE) {
			return Predicate._FALSE;
		}
		Formula f = new Formula(_f1, _f2, Connector.AND);
		return f;
	}

	private static Formula simplifyOR(Formula _f1, Formula _f2) {
		if (_f1 == Predicate._TRUE) {
			return Predicate._TRUE;
		}
		if (_f2 == Predicate._TRUE) {
			return Predicate._TRUE;
		}
		if ((_f1 == Predicate._FALSE) && (_f2 == Predicate._FALSE)) {
			return Predicate._FALSE;
		}
		if (_f1 == Predicate._FALSE) {
			return _f2;
		}
		if (_f2 == Predicate._FALSE) {
			return _f1;
		}
		Formula f = new Formula(_f1, _f2, Connector.OR);
		return f;
	}

	private static Formula simplifyIMPLIES(Formula _f1, Formula _f2) {
		if (_f2 == Predicate._TRUE) {
			return Predicate._TRUE;
		}
		if (_f1 == Predicate._FALSE) {
			return Predicate._TRUE;
		}
		Formula f = new Formula(_f1, _f2, Connector.IMPLIES);
		return f;
	}

	public Formula() {
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
			subformulas[i] = subformulas[i].substitute(_e, _v.copy());
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
		String op = "";
		if (connector == Connector.AND) {
			op = " && ";
		}
		if (connector == Connector.OR) {
			op = " || ";
		}
		if (connector == Connector.IMPLIES) {
			op = " ==> ";
		}
		if (connector == Connector.NOT) {
			op = " ! ";
		}

		if (subformulas.length == 1) {
			return "(" + op + subformulas[0] + ")";
		} else {
			String s = "" + subformulas[0];
			for (int i = 1; i < subformulas.length; i++) {
				s = s + op + subformulas[i];
			}
			return s;
		}
	}

}

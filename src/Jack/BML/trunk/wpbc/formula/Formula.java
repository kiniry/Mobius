/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Formula  {
	
	private Formula[] subformulas;
	
	private byte connector;
	
	public Formula() {	
	}
	
	public Formula(Formula[] _f , byte _conn) {
		setConnector(_conn);
		subformulas = _f;
	}
	
	public Formula(Formula _left, Formula _right, byte _conn) {
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
	private  void setConnector(byte connector) {
		this.connector = connector;
	}

	/**
	 * substitute the expression _e in this formula by the expression _v
	 * @param _e
	 * @param _v
	 * @return  this[ _e <- _v]
	 */
	public Formula substitute(Expression _e,  Expression _v) {
		for (int i = 0; i < subformulas.length; i++  ) {
			subformulas[i].substitute(_e, _v);
		}
		return this;
	}
	
	public Formula copy() {
		Formula[]  _subformulas= new Formula[subformulas.length];
		for (int i = 0; i < subformulas.length; i++) {
			_subformulas[i] = subformulas[i].copy();
		}
		Formula _copy = new Formula(_subformulas, connector);
		return _copy;
	}

}

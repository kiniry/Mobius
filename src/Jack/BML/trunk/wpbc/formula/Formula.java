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
	
	private Formula left;
	private Formula right;
	private byte connector;
	
	public Formula() {	
	}
	
	public Formula(Formula _left, Formula _right, byte _conn) {
		setLeft(_left);
		setRight(_right);
		setConnector(_conn);
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
	 * @return Returns the left.
	 */
	public Formula getLeft() {
		return left;
	}
	/**
	 * @param left The left to set.
	 */
	protected void setLeft(Formula left) {
		this.left = left;
	}
	/**
	 * @return Returns the right.
	 */
	public Formula getRight() {
		return right;
	}
	/**
	 * @param right The right to set.
	 */
	private void setRight(Formula right) {
		this.right = right;
	}
	
	public Formula substitute(Expression __e, Object value) {
		return null;
	}
}

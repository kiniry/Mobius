/*
 * Created on Mar 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.bcclass.attributes;

import bytecode_wp.bcexpression.Expression;

/**
 * 
 */
public class SET {

	//private int bcPos;
	private Expression lExpr1;
	private Expression rExpr2;
	
	/**
	 * @deprecated use {@link #SET(Expression, Expression)} instead.
	 */
	public SET( int _bcPos, Expression _lExpr1, Expression _rExpr2) {
		//bcPos = _bcPos;
		this( _lExpr1, _rExpr2);
	}

	public SET(Expression _lExpr1, Expression _rExpr2) {
		lExpr1 = _lExpr1;
		rExpr2 = _rExpr2;
	}

	/**
	 * @return
	 */
	public Expression getAssignTo() {
		return lExpr1;
	}


	/**
	 * @return
	 */
	public Expression getAssignedVar() {
		return rExpr2;
	}
	

	


}

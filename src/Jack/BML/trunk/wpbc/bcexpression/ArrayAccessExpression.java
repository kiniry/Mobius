/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ArrayAccessExpression extends CPExpression {
	private int arrIndex;
	
	//referenece to an array object
	private Expression left;
	
	public ArrayAccessExpression(Expression  _left, int _arrIndex  ) {
		setLeft(_left);
		setArrIndex(_arrIndex);
	}

	/**
	 * @param index2
	 */
	private void setArrIndex(int index2) {
		arrIndex= index2;
	}
	
	public int getArrIndex() {
		return arrIndex;
	}
	/**
	 * @param right2
	 */
	public void setLeft(Expression _left) {
		left = _left;
		
	}
	
}

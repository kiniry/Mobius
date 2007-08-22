/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package annot.vm;


import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;




/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public final class Stack extends Expression  {
	
//	private Expression counter;
	
	public Stack(Expression _counter) {
		super(_counter);
	}
	
	/*
	 * this expression has the Top type, i.e. it may receive as value any other expression of any type 
	 *  (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {		
	}


	public String printCode1(BMLConfig conf) {
		return "Stack(" + getSubExpressions()[0].toString() + ")"; 
	}

//
//	
//	/**
//	 * the substitution can be realised in 3 ways :
//	 * if _e1 equals this object and this[_e1<-- _e2 ] = _e2
//	 * else recursively do the substitution in the subexpression counter 
//	 * 		and replace the old counter by the new one counter = counter[_e1<-- _e2 ]
//	 */
//	public  Expression substitute(Expression _e1, Expression _e2){
////		Util.dump("Stack.substitute in  " + toString() + "    " + _e1.toString() + " by " + _e2.toString()) ;
//	
//		if (this.equals(_e1) ) {
//			return _e2.copy();
//		}
//		
//		Expression counter =getSubExpressions()[0];
//		counter = counter.substitute( _e1, _e2);
//		setSubExpressions(new Expression[]{counter});
//		return this;
//	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression counter = getSubExpressions()[0];
		Expression copyCounter = counter.copy();
		Stack  copy = new Stack(copyCounter);
		return copy;
	}
		
}

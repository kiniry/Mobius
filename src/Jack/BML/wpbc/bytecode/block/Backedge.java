/*
 * Created on Feb 22, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode.block;

import sun.security.krb5.internal.rcache.ba;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Backedge {
	
	private int number ;
	private int startBackEdge;
	private int endBackEdge;
	
	public Backedge(int _startBackEdge, int _endBackEdge) {
		startBackEdge = _startBackEdge;
		endBackEdge = _endBackEdge;
	}

	/**
	 * @return Returns the endBackEdge.
	 */
	public int getEndBackEdge() {
		return endBackEdge;
	}
	
	/**
	 * @return Returns the startBackEdge.
	 */
	public int getStartBackEdge() {
		return startBackEdge;
	}
	
	public void setNumber(int number) {
		this.number = number;
	}
	
	
//
//	/**
//	 *  
//	 * @param backedge
//	 * @return true if this loop is entered before  backedge 
//	 */
//	public boolean isEnteredBefore( Backedge backedge) {
//		int _end = backedge.getEndBackEdge();
//		int _start = backedge.getStartBackEdge();
//		
//		// backdge is nested in this loop
//		if ((getStartBackEdge() > _start ) && (getEndBackEdge() < _end) ) {
//			return true;
//		}
//		// backedge is after this loop
//		if ( (getStartBackEdge() > _end )&& ( getStartBackEdge() > _start )) {
//			return true;
//		}
//		return false;
//	}
	
	/**
	 * @return Returns the number.
	 */
	public int getNumber() {
		return number;
	}
	
	public String toString( ) {
		return "backedgeStart=" + startBackEdge + ": backedgeEnd=" + endBackEdge;
	}
}

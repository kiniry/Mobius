/*
 * Created on Sep 30, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class P {
	public P a;
	public int b;
	
	//@requires p.b == 3;
	//@ ensures p.a.a.a.b == 3;
	public void m(P p) {
		p.a = p;
	}
	
}

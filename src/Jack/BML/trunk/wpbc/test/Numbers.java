/*
 * Created on Apr 16, 2004
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
public class Numbers {

	public static void main(String[] args) {
		System.out.println("00000000FFFFFFFF  =  " + Long.parseLong("00000000FFFFFFFF", 16));
		Long l = new Long("00000000FFFFFFFF");
		System.out.println(" long value "  + l.longValue());
	}
}

/*
 * Created on Jan 20, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class UnderFlow {

	public static void main1(String[] args) {
		int min1 = Integer.MIN_VALUE + 1;
		int min2 = Integer.MIN_VALUE + 2;
		int sum = min1 + min2;
		System.out.println(  "min1 + min2  " + sum );
		System.out.println(  "min1 + min2  " +  min1);
		System.out.println(  "min1 + min2  " +  min2 );
	}
	
	public static void main(String[] args) {
		int max1 = Integer.MAX_VALUE + 1;
		System.out.println(  "Integer.MAX_VALUE + 1 = " +  Integer.MAX_VALUE );
		System.out.println(  "max1 = " +  max1 );
	}
    
	

}

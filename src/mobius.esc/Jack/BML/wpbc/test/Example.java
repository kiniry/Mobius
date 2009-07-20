/*
 * Created on Jan 27, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

public class Example {

	
   public static boolean k() {
   		int k = 1 / 0;
       return true;
   }

   public static void m(boolean b) {
       while (b ) {
           try{
               b = k();
           } finally {
           		if (b) continue;
           }
       }
   }

   public static void main(String[] args) {
   	
           m( true );
  }
}
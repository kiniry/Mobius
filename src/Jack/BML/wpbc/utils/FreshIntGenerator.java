/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package utils;

import java.util.Random;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class FreshIntGenerator {
	private static int random = 0;
	
	public static int getInt() {
		return random++;
	}
	
}

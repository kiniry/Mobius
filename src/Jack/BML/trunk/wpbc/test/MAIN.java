/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package test;

import bcclass.BCClass;
import application.JavaApplication;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class MAIN  {
	
	public static void main(String[] args) {
		BCClass clazz = JavaApplication.Application.getClass("test.A");
//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	// Moore example
	public static void main1(String[] args) {
			BCClass clazz = JavaApplication.Application.getClass("test.Half");
//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
	}
}

/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package test;

import bc.io.ReadAttributeException;
import bcclass.BCClass;
import application.JavaApplication;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class MAIN {
	
	public static void main15(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.BCMethod");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	public static void main37(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.F");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main10(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.Modulo");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main9(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.A");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main11(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.G");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main21(String[] args) {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.P");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}

	// Moore example
	public static void main(String[] args) throws ReadAttributeException {
		BCClass clazz = JavaApplication.Application.getClass("test.Half");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
}

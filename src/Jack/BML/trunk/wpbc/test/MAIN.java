/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package test;

import bc.io.ReadAttributeException;
import bcclass.BCClass;
import bytecode.block.IllegalLoopException;
import application.JavaApplication;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class MAIN {
	
	public static void main15(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.BCMethod");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	public static void main37(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.F");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void mainModulo(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.Modulo");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main9(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.A");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main11(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.G");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	public static void main21(String[] args) throws IllegalLoopException {
		try {
			BCClass clazz = JavaApplication.Application.getClass("test.P");
			//		BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
			clazz.wp();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}

	// Moore example
	public static void mainHalf(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Half");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	
	public static void main3(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Memory");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void mainarr00102(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("arr.arr00102");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void mainarr02202(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("arr.arr02202");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void main100(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Arr");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void mainBinc01802(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("Binc.binc01802");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}

	public static void mainExample(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Example");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void mainFinally(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Finally");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	

	public static void mainTEstLoops(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.TestLoops");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}


	public static void mainA(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.A");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	

	public static void mainM(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.M");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	}
	
	public static void mainSquare(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.Square");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	} 
	
	//ExampleBV  -- a loop 	caused by jsr
	public static void mainBV(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.ExampleBV");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	} 
	
//	ExampleBV  -- a loop 	caused by jsr
	public static void main(String[] args) throws ReadAttributeException, IllegalLoopException {
		BCClass clazz = JavaApplication.Application.getClass("test.MethCall");
		//			BCClass clazz = JavaApplication.Application.getClass("bytecode.objectmanipulation.BCInvoke");
		clazz.wp();
	} 
}

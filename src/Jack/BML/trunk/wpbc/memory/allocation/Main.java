/*
 * Created on Feb 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package memory.allocation;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;

import application.JavaApplication;
import bc.io.ReadAttributeException;
import bcclass.BCClass;
import bcclass.BCMethod;
import bytecode.block.IllegalLoopException;

/**
 * @author mpavlova
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class Main {

	/**
	 * test.A.class tested
	 * 
	 * @param args
	 * @throws MalformedException
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 */
	public static void main(String[] args) throws MalformedException, ReadAttributeException, IllegalLoopException {
				BCClass clazz =
		 JavaApplication.Application.getClass("test.MemoryLoop");
//					JavaApplication.Application.getClass("memory.allocation.MethodAllocation");
					//		 
		//		BCClass clazz =
		// JavaApplication.Application.getClass("bcexpression.overload.FormulaOverload");
		//		BCClass clazz =
		// JavaApplication.Application.getClass("org.apache.bcel.classfile.JavaClass"
		// );
		//		BCClass clazz =
		// JavaApplication.Application.getClass("test.DetectLoops");
//		BCClass clazz = JavaApplication.Application
//				.getClass("java.lang.Integer");

//		//comment / doesnot work as there are mutually recursive calls 
//		// between java.lang.String.<init>([CII)V and java.lang.Integer.toUnsignedString(II)Ljava/lang/String;
//		BCClass clazz = JavaApplication.Application
//		.getClass("test.StringTest");

		
//		BCClass clazz = JavaApplication.Application.getClass("test.MemoryNestedLoop");

		initMethodAlloc(clazz);
		getMemoryForMethodsInClass(clazz);
		setSpec();
		/*clazz.wp();
*/	}

/*	public static BCMethod initParticularMethod(BCClass _class)
			throws ReadAttributeException, IllegalLoopException {
		Iterator miter = _class.getMethods().iterator();
		BCMethod m = null;
		while (miter.hasNext()) {
			m = (BCMethod) miter.next();
			if (m.getName().equals("toUnsignedString")) {
				break;
			}
		}
		m.initMethod();
		return m;
	}
*/
	
	public static void getMemoryForMethodsInParticularMathod(BCMethod m) throws ReadAttributeException, IllegalLoopException, MalformedException {
		int memoryAllocated = MethodAllocation.getMethodAllocates(m);
	}

	public static void initMethodAlloc(BCClass _class)
			throws ReadAttributeException, IllegalLoopException {
		Iterator miter = _class.getMethods().iterator();
		while (miter.hasNext()) {
			BCMethod m = (BCMethod) miter.next();
			m.initMethod();
		}
	}

	public static void getMemoryForMethodsInClass(BCClass _class)
			throws ReadAttributeException, IllegalLoopException, MalformedException {
		Iterator miter = _class.getMethods().iterator();
		while (miter.hasNext()) {
			BCMethod m = (BCMethod) miter.next();
			/*
			 * System.out.println(" search allocations for method " +
			 * m.getName() );
			 */
			int memoryAllocated = MethodAllocation.getMethodAllocates(m);

		}
	}
	
	/** 
	 * sets the specification for every method that belongs to any class
	 * that appears in the method 
	 */
	public static void setSpec() {
		Enumeration classes  = JavaApplication.Application.getClasses();  
		while (classes.hasMoreElements() ) {
			BCClass  bcc = (BCClass)classes.nextElement();
			Iterator c  = bcc.getMethods().iterator();
			while (c.hasNext()) {
				BCMethod m =(BCMethod)c.next();
				m.initMethodSpecForMemoryConsumption();
			}
		}
	}
}
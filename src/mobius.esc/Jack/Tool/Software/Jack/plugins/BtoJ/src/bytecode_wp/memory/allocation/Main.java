/*
 * Created on Feb 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.memory.allocation;

import java.util.Iterator;

import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bytecode.block.IllegalLoopException;

/**
 * @author M. Pavlova
 *
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
/*				BCClass clazz =*/
					/*JavaClassLoader.Application.getClass("test.MemoryLoop");
*///					JavaApplication.Application.getClass("memory.allocation.MethodAllocation");
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

/*		initMethodAlloc(clazz);
		getMemoryForMethodsInClass(clazz);
		setSpec();
		clazz.wp();*/
	}

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
	
	/**
	 * Basically calls {@link MethodAllocation#getMethodAllocates(BCMethod)}
	 * with <code>m</code> as a parameter.
	 * @param m
	 */
	//@ modifies \nothing;
	public static void getMemoryForMethodsInParticularMathod(BCMethod m) throws ReadAttributeException, IllegalLoopException, MalformedException {
		//int memoryAllocated = 
			MethodAllocation.getMethodAllocates(m);
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
			 * Logger.get().println(" search allocations for method " +
			 * m.getName() );
			 */
			//int memoryAllocated = 
			MethodAllocation.getMethodAllocates(m);

		}
	}
	
	/** 
	 * sets the specification for every method that belongs to any class
	 * that appears in the method 
	 */
	public static void setSpec() {
	/*	while (classes.hasMoreElements() ) {
			BCClass  bcc = (BCClass)classes.nextElement();
			Iterator c  = bcc.getMethods().iterator();
			while (c.hasNext()) {
				BCMethod m =(BCMethod)c.next();
				m.initMethodSpecForMemoryConsumption();
			}
		}*/
	}
}
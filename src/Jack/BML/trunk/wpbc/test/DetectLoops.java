/*
 * Created on Feb 25, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassQueue;
import org.apache.bcel.util.ClassVector;

/**
 * @author Mariela
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class DetectLoops {

//	public void m() {
//
//		ClassQueue queue = new ClassQueue();
//		ClassVector vec = new ClassVector();
//
//		while (!queue.empty()) {
//			JavaClass clazz = queue.dequeue();
//
//			JavaClass souper = clazz.getSuperClass();
//			JavaClass[] interfaces = clazz.getInterfaces();
//
//			if (clazz.isInterface()) {
//				vec.addElement(clazz);
//			} else {
//				if (souper != null) {
//					queue.enqueue(souper);
//				}
//			}
//
//			for (int i = 0; i < interfaces.length; i++) {
//				queue.enqueue(interfaces[i]);
//			}
//		}
//	}

	public void m() {

		A queue = new A();
		ClassVector vec = new ClassVector();

		while (!queue.empty()) {
			JavaClass clazz = queue.dequeue();

//			JavaClass souper = clazz.getSuperClass();
//			JavaClass[] interfaces = clazz.getInterfaces();

			if (clazz.isInterface()) {
				vec.addElement(clazz);
			} else {
				if (queue != null) {
					queue.enqueue(new A());
				}
			}

			for (int i = 0; i < 100; i++) {
				queue.enqueue(new A());
			}
		}
	}


}
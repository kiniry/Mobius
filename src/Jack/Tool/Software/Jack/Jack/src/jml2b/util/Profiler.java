///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Profiler.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.util;

import jack.util.Logger;

//import java.util.Enumeration;
//import java.util.Hashtable;

/**
 * This class allows to profile the memory usage of JACK.
 * By default it is commented.
 * @author L. Burdy
 */
public class Profiler {

	//	static Hashtable ht = new Hashtable();
	//	public static int counter = 0;
	//
	//	public Profiler() {
	//		if (ht.containsKey(getClass())) {
	//			ht.put(
	//				getClass(),
	//				new Integer(((Integer) ht.get(getClass())).intValue() + 1));
	//		} else {
	//			ht.put(getClass(), new Integer(1));
	//		}
	//		counter++;
	//		//		if ((Runtime.getRuntime().freeMemory() < 300000
	//		//			&& Runtime.getRuntime().freeMemory() % 10000 == 0) ||
	//		//            counter % 100000 == 0) {
	//		//			display();
	//		//            Logger.get().println("Counter " + counter);
	//		//            Logger.get().println(
	//		//                "Mem "
	//		//                    + Runtime.getRuntime().freeMemory()
	//		//                    + "/"
	//		//                    + Runtime.getRuntime().totalMemory()
	//		//                    + " ("
	//		//                    + Runtime.getRuntime().freeMemory()
	//		//                        * 100
	//		//                        / Runtime.getRuntime().totalMemory()
	//		//                    + "%)");
	//		//            }
	//	}
	//
	//	public void finalize() {
	//		ht.put(
	//			getClass(),
	//			new Integer(((Integer) ht.get(getClass())).intValue() - 1));
	//	}
	//
	//	public static void display() {
	//		Enumeration e = ht.keys();
	//		while (e.hasMoreElements()) {
	//			java.lang.Class c = (java.lang.Class) e.nextElement();
	//			try {
	//				Logger.get().println(
	//					c.toString()
	//						+ ": "
	//						+ ht.get(c).toString());
	//			} catch (Exception ee) {
	//			}
	//		}
	//	}

	//	public static int sizeOf(java.lang.Class c) throws Exception {
	//		// Warm up all classes/methods we will use
	//		runGC();
	//		usedMemory();
	//
	//		// Array to keep strong references to allocated objects
	//		final int count = 100000;
	//		Object[] objects = new Object[count];
	//
	//		long heap1 = 0;
	//
	//		// Allocate count+1 objects, discard the first one
	//		for (int i = -1; i < count; ++i) {
	//
	//			// Instantiate your data here and assign it to object
	//			Object object = c.newInstance();
	//
	//			//object = new TerminalExp();
	//			//object = new Integer (i);
	//			//object = new Long (i);
	//			//object = new String ();
	//			//object = new byte [128][1]
	//
	//			if (i >= 0)
	//				objects[i] = object;
	//			else {
	//				object = null; // Discard the warm up object
	//				runGC();
	//				heap1 = usedMemory(); // Take a before heap snapshot
	//			}
	//		}
	//
	//		runGC();
	//		long heap2 = usedMemory(); // Take an after heap snapshot:
	//
	//		final int size = Math.round(((float) (heap2 - heap1)) / count);
	//		//        Logger.get().println ("'before' heap: " + heap1 +
	//		//                            ", 'after' heap: " + heap2);
	//		//        Logger.get().println ("heap delta: " + (heap2 - heap1) +
	//		//            ", {" + objects [0].getClass () + "} size = " + size + " bytes");
	//
	//		for (int i = 0; i < count; ++i)
	//			objects[i] = null;
	//		objects = null;
	//		return size;
	//	}

	public static void runGC() {
		// It helps to call Runtime.gc()
		// using several method calls:
		for (int r = 0; r < 4; ++r)
			_runGC();
		Logger.err.println("Used memory: " + usedMemory());
	}

	private static void _runGC() {
		long usedMem1 = usedMemory(), usedMem2 = Long.MAX_VALUE;
		for (int i = 0;(usedMem1 < usedMem2) && (i < 500); ++i) {
			s_runtime.runFinalization();
			s_runtime.gc();
			//			Thread.currentThread().yield();

			usedMem2 = usedMem1;
			usedMem1 = usedMemory();
		}
	}

	private static long usedMemory() {
		return s_runtime.totalMemory() - s_runtime.freeMemory();
	}

	private static final Runtime s_runtime = Runtime.getRuntime();

}

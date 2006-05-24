///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Tabs.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.util;


/** 
 * Simple class that simplifies handling tabs. 
 * It is used to pretty-print the tree.
 * @author A. Requet
 */
public class Tabs extends Profiler {
    /// current number of tabs
    private /*@ spec_public */
    int tabCount;
    /// size of a tab
    private int tabSize;
    /// default tab size
    public static final int DEFAULT_TAB_SIZE = 4;

    /*@
      @ invariant tabCount >= 0;
      @ private invariant tabSize  >= 0;
      @ invariant DEFAULT_TAB_SIZE == 4;
      @*/

    public Tabs() {
        this(DEFAULT_TAB_SIZE);
    }

    //@ requires size >= 0;
    Tabs(int size) {
        tabSize = size;
        tabCount = 0;
    }

	//@ modifies tabCount;
    public void inc() {
        ++tabCount;
    }

    //@ requires tabCount > 0;
	//@ modifies tabCount;
    public void dec() {
        --tabCount;
    }

    /** convert the given set of tabs to a string.
     */
    public String toString() {
        int space_count = tabCount * tabSize;
        StringBuffer tmp = new StringBuffer(space_count);

		//@ loop_invariant true;
		//@ loop_exsures (RuntimeException re) false;
        for (int i = 0; i < space_count; ++i) {
            tmp.append(" ");
        }
        return tmp.toString();
    }
}

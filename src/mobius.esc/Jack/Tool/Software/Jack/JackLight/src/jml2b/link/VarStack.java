///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: VarStack.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.link;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.structure.java.Field;
import jml2b.util.Profiler;

/**
 * This class implements a stack containing sets of fields. It is used in the
 * context during the link.
 * 
 * @author A. Requet
 */
public class VarStack extends Profiler {
	
	/**
	 * The stack of sets. Elements are <code>Vector</code> that contains
	 * <code>Field</code>
	 */
	Vector stack;

	/*@
	  @ invariant stack != null;
	  @*/

	/**
	 * Creates a new empty stack.
	 */
	public VarStack() {
		stack = new Vector();
	}

	/** 
	 * Add a new set of fields to the top of the stack.
	 * 
	 * @param v The set of field to add to the current block
	 **/
	/*@
	  @ requires v != null;
	  @*/
	public void add(Vector v) {
		Vector t = top();
		Enumeration e = v.elements();

		/*@
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			t.add(e.nextElement());
		}
	}

	/**
	 * Add a field to the set on the top of the stack.
	 * 
	 * @param f The field to add.
	 */
	public void add(Field f) {
		top().add(f);
	}

	/**
	 * Create a new empty set of fields at the top of the stack.
	 *
	 **/
	public void pushVars() {
		stack.addElement(new Vector());
	}

	/**
	 * Remove the elemùent at the top of the stack.
	 *
	 **/
	public void popVars() {
		stack.remove(stack.size() - 1);
	}

	/**
	 * Returns whether the stack is empty or not.
	 **/
	public boolean empty() {
		return stack.isEmpty();
	}

	/**
	 * Return the field with the given name. <code>null</code> if the field is 
	 * not found
	 * @param name The name of the field
	 * @return
	 */ 
	public Field getField(String name) {
		// search from a field from the top of the name stack
		/*@
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = stack.size() - 1; i >= 0; --i) {
			Vector v = (Vector) stack.get(i);
			Enumeration e = v.elements();
			/*@
			@ loop_invariant true;
			@ loop_exsures (RuntimeException) false;
			@*/
			while (e.hasMoreElements()) {
				Field f = (Field) e.nextElement();
				if (name.equals(f.getName())) {
					// found
					return f;
				}
			}
		}

		// not found
		return null;
	}

	/**
	 * Returns the top of the stack.
	 * @return
	 **/
	public Vector top() {
		return (Vector) stack.get(stack.size() - 1);
	}

	/**
	 * Returns the elements of the stack.
	 * @return
	 **/
	public Enumeration elements() {
		if (stack.size() == 0)
			return stack.elements();
		else
			return ((Vector) stack.get(stack.size() - 1)).elements();
	}

}

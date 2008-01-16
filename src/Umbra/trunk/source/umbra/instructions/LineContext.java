/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2007-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Stack;

/**
 * @author alx
 *
 */
public class LineContext {

  public static final int STATE_UNDEFINED = 0;
  private static final int STATE_INITIAL = 1;
  private static final int STATE_CLASS_TO_BE_READ = 2;
  private static final int STATE_INSIDE_COMMENT = 3;

  private int my_state;
  private Stack my_state_stack;

  public LineContext() {
    my_state = STATE_INITIAL;
    my_state_stack = new Stack();
  }

  public void setInitial() {
    my_state = STATE_INITIAL;
  }

  public void seClassToBeRead() {
      my_state = STATE_CLASS_TO_BE_READ;
  }

  public boolean isInsideComment() {
    return my_state == STATE_INSIDE_COMMENT;
  }

  public void setState(int a_state) {
    my_state = a_state;
  }

  public int getState() {
    return my_state;
  }

  public void setInsideComment() {
    my_state = STATE_INSIDE_COMMENT;
  }

  public void rememberState() {
    my_state_stack.push(new Integer(my_state));
  }
  
  public void revertState() {
    my_state = ((Integer)my_state_stack.pop()).intValue();
  }
}

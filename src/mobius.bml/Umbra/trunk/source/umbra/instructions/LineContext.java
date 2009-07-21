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
 * The line parser on which the parsing of the byte code textual representation
 * is based is context sensitive. In particular this representation can contain
 * multi-line comments the contents of which should not be parsed. This class
 * allows to keep track of all such issues. Currently it handles the cases when
 * the parsing is:
 * <ul>
 *   <li>at the beginning of a text file,</li>
 *   <li>parses a class representation,</li>
 *   <li>parses a multi-line comment,</li>
 *   <li>parses a annotation comment.</li>
 * </ul>
 * Additionally, this keeps track of the parsed methods.
 * This can be extended in the futer to handle line number table etc.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class LineContext {

  /**
   * The context state which is used to mark an error situation.
   */
  public static final int STATE_UNDEFINED = 0;

  /**
   * The context state which is used at the beginning of parsing.
   */
  private static final int STATE_INITIAL = 1;

  /**
   * The context state which is used inside constant pools.
   */
  private static final int STATE_CONSTANT_POOL = 2;

  /**
   * The context state which is used in case we expect that the fields
   * of a class will be read.
   */
  private static final int STATE_FIELDS_TO_BE_READ = 3;

  /**
   * The context state which is used in case we expect that the methods
   * of a class will be read.
   */
  private static final int STATE_METHODS_TO_BE_READ = 4;

  /**
   * The context state which is uset in case the parsing is inside of a
   * multi-line comment.
   */
  private static final int STATE_INSIDE_COMMENT = 5;

  /**
   * The context state which is used in case the parsing is inside of a
   * BML annotation comment.
   */
  private static final int STATE_INSIDE_ANNOTATION = 6;

  /**
   * The context state which is used in case the parsing is inside of a
   * method.
   */
  private static final int STATE_INSIDE_METHOD = 7;

  /**
   * The context state which is used in case the parsing is inside of the
   * invariant area of the class.
   */
  private static final int STATE_INVARIANT_AREA = 8;

  /**
   * The current state of the context.
   */
  private int my_state;

  /**
   * The stack of states used to handle the parsing of comments.
   */
  private Stack my_state_stack;

  /**
   * The number of the currently parsed method. It contains -1 in case the
   * method number has not been set yet.
   */
  private int my_method;

  /**
   * The last line in the annotation.
   */
  private int my_annotation_end;


  /**
   * The constructor initialises the internal state of the object so that it
   * is in the internal state. It also initialises the stack of states which
   * must be reverted.
   */
  public LineContext() {
    setInitial();
    my_state_stack = new Stack();
    my_method = -1;
  }

  /**
   * This method sets the internal state of the object to the initial value.
   */
  public void setInitial() {
    my_state = STATE_INITIAL;
  }

  /**
   * The method sets the internal state of the object to the state in which
   * we are about to parse the fields.
   */
  public void setFieldsToBeRead() {
    my_state = STATE_FIELDS_TO_BE_READ;
  }

  /**
   * The method sets the internal state of the object to the state in which
   * we are about to parse the methods.
   */
  public void setMethodsToBeRead() {
    my_state = STATE_METHODS_TO_BE_READ;
  }

  /**
   * The method sets the internal state of the object to the state in which
   * we are about to parse class fields.
   */
  public void setFieldArea() {
    my_state = STATE_FIELDS_TO_BE_READ;
  }

  /**
   * Returns <code>true</code> when the object is in the state inside a comment.
   *
   * @return <code>true</code> when the object is in the state inside a comment
   *   <code>false</code> otherwise
   */
  public boolean isInsideComment() {
    return my_state == STATE_INSIDE_COMMENT;
  }

  /**
   * Returns the current state of the line context.
   *
   * @return the current state of the line context
   */
  public int getState() {
    return my_state;
  }

  /**
   * Sets the current state to be the state inside a comment. Additionally,
   * this method remembers the current state so that it can be restored
   * by {@link #revertState()}.
   */
  public void setInsideComment() {
    rememberState();
    my_state = STATE_INSIDE_COMMENT;
  }

  /**
   * It remembers the current state on the history stack state. This
   * functionality is needed to implement comments.
   */
  public void rememberState() {
    my_state_stack.push(new Integer(my_state));
  }

  /**
   * It restores from the history stack the previously remebered state. This
   * functionality is needed to implement comments.
   */
  public void revertState() {
    my_state = ((Integer)my_state_stack.pop()).intValue();
  }

  /**
   * Returns <code>true</code> when the object is in the state inside an
   * annotation.
   *
   * @return <code>true</code> when the object is in the state inside an
   *   annotation <code>false</code> otherwise
   */
  public boolean isInsideAnnotation() {
    return my_state == STATE_INSIDE_ANNOTATION;
  }

  /**
   * Sets the current state to be the state inside an annotation. Additionally,
   * this method remembers the current state so that it can be restored
   * by {@link #revertState()}.
   *
   * @param a_pos the last editor line of the annotation to be parsed or -1
   */
  public void setInsideAnnotation(final int a_pos) {
    rememberState();
    my_annotation_end = a_pos;
    my_state = STATE_INSIDE_ANNOTATION;
  }

  /**
   * This method advances by 1 the method number counter. Note that initially
   * the method number is -1.
   */
  public void incMethodNo() {
    my_method++;
  }

  /**
   * This method returns the current method number.
   *
   * @return the current method number
   */
  public int getMethodNo() {
    return my_method;
  }

  /**
   * This method initialises the internal method number to the given value.
   *
   * @param a_methodno the method number to be set
   */
  public void setMethodNo(final int a_methodno) {
    my_method = a_methodno;
  }

  /**
   * Returns the value of the remembered annotation end position.
   *
   * @return the annotation end position
   */
  public int getAnnotationEnd() {
    return my_annotation_end;
  }

  /**
   * Sets the current state to be the state inside method.
   */
  public void setInsideMethod() {
    my_state = STATE_INSIDE_METHOD;
  }

  /**
   * Sets the current state to be the state inside the invariant area.
   */
  public void setInvariantArea() {
    my_state = STATE_INVARIANT_AREA;
  }

  /**
   * Sets the current state to be the state inside the constant pool.
   */
  public void setInsideCP() {
    my_state = STATE_CONSTANT_POOL;
  }

  /**
   * Returns <code>true</code> when the object is in the state inside the
   * invariant area.
   *
   * @return <code>true</code> when the object is in the state inside the
   *   invariant area, <code>false</code> otherwise
   */
  public boolean isInInvariantArea() {
    return my_state == STATE_INVARIANT_AREA;
  }

  /**
   * Returns <code>true</code> when the object is in the state inside the
   * area of fields.
   *
   * @return <code>true</code> when the object is in the state inside the
   *   field area, <code>false</code> otherwise
   */
  public boolean isInFieldsArea() {
    return my_state == STATE_FIELDS_TO_BE_READ;
  }

  /**
   * Returns <code>true</code> when the object is in the state inside the
   * method.
   *
   * @return <code>true</code> when the object is in the state inside a
   *   method, <code>false</code> otherwise
   */
  public boolean isInsideMethod() {
    return my_state == STATE_INSIDE_METHOD;
  }

  /**
   * Returns <code>true</code> when the object is in the state inside the
   * constant pool.
   *
   * @return <code>true</code> when the object is in the state inside the
   *   constant pool, <code>false</code> otherwise
   */
  public boolean isInsideConstantPool() {
    return my_state == STATE_CONSTANT_POOL;
  }

}

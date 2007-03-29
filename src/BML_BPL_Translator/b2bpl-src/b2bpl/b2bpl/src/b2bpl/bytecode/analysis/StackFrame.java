package b2bpl.bytecode.analysis;

import b2bpl.bytecode.JType;


/**
 * Simple class representing a JVM stack frame.
 *
 * <p>
 * Every stack frame consists of a set of types for the local variables and the
 * elements on the operand stack.
 * </p>
 *
 * @author Ovidio Mallo
 */
public class StackFrame {

  /** The types of the local variables. */
  private JType[] locals;

  /**
   * The types of the elements on the operand stack. Only the elements in the
   * index range {@code [0, top)} are in use and thus valid.
   */
  private JType[] stack;

  /** Index pointing to one element beyond the top of the operand stack. */
  private int top;

  /**
   * Creates a new stack frame for {@code localCount} local variables and a
   * capacity of at most {@code maxStackSize} stack elements.
   *
   * @param localCount    The number of local variables of the stack frame.
   * @param maxStackSize  The maximal number of stack elements the stack frame
   *                      should be able to hold.
   */
  public StackFrame(int localCount, int maxStackSize) {
    locals = new JType[localCount];
    stack = new JType[maxStackSize];
    top = 0;
  }

  /**
   * Returns the number of local variables.
   *
   * @return  The number of local variables.
   */
  public int getLocalCount() {
    return locals.length;
  }

  /**
   * Returns the type of the local variable with the given {@code index}.
   *
   * @param index  The index of the local variable.
   * @return       The type of the local variable with the given {@code index}.
   */
  public JType getLocal(int index) {
    return locals[index];
  }

  /**
   * Sets the type of the local variable with the given {@code index} to
   * {@code type}.
   *
   * @param index  The index of the local variable.
   * @param type   The type to set for the local variable with the given
   *               {@code index}.
   */
  public void setLocal(int index, JType type) {
    locals[index] = type;
  }

  /**
   * Returns the number of stack elements.
   *
   * @return  The number of stack elements.
   */
  public int getStackSize() {
    return top;
  }

  /**
   * Returns the maximal number of stack elements this frame can hold.
   *
   * @return  The maximal number of stack elements this frame can hold.
   */
  public int getMaxStackSize() {
    return stack.length;
  }

  /**
   * Returns the type of the topmost stack element.
   *
   * @return  The type of the topmost stack element.
   */
  public JType peek() {
    return stack[top - 1];
  }

  /**
   * Returns the type of the stack element at the given {@code index} (where
   * counting starts at the <i>bottom</i> of the stack).
   *
   * @return  The type of the stack element at the given {@code index}.
   */
  public JType peek(int index) {
    return stack[index];
  }

  /**
   * Returns and removes the type of the topmost stack element.
   *
   * @return  The type of the topmost stack element.
   */
  public JType pop() {
    return stack[--top];
  }

  /**
   * Pushes the given {@code type} on the top of the operand stack.
   *
   * @param type  The type to push on the top of the operand stack.
   */
  public void push(JType type) {
    stack[top++] = type;
  }

  /**
   * Removes all the elements from the operand stack.
   */
  public void clearStack() {
    top = 0;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append('[');
    for (int i = 0; i < locals.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(locals[i]);
    }
    sb.append(']');

    sb.append('[');
    for (int i = 0; i < top; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(stack[i]);
    }
    sb.append(']');

    return sb.toString();
  }
}

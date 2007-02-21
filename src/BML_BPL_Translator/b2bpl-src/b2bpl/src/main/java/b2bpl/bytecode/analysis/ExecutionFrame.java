package b2bpl.bytecode.analysis;

import b2bpl.bytecode.JType;


public class ExecutionFrame {

  private JType[] locals;

  private JType[] stack;

  private int top;

  public ExecutionFrame(int localCount, int maxStackSize) {
    super();
    this.locals = new JType[localCount];
    this.stack = new JType[maxStackSize];
    top = 0;
  }

  public int getLocalCount() {
    return locals.length;
  }

  public JType getLocal(int index) {
    return locals[index];
  }

  public void setLocal(int index, JType type) {
    locals[index] = type;
  }

  public int getStackSize() {
    return top;
  }

  public int getMaxStackSize() {
    return stack.length;
  }

  public JType peek() {
    return stack[top - 1];
  }

  public JType peek(int index) {
    return stack[index];
  }

  public JType pop() {
    return stack[--top];
  }

  public void push(JType type) {
    stack[top++] = type;
  }

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

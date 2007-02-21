package b2bpl.bytecode;

import java.util.Iterator;


public class Instructions implements Iterable<InstructionHandle> {

  private InstructionHandle first;

  private InstructionHandle last;

  private int size = 0;

  private InstructionHandle[] array;

  public InstructionHandle getFirst() {
    return first;
  }

  public InstructionHandle getLast() {
    return last;
  }

  public void add(InstructionHandle instruction) {
    instruction.setNext(null);
    instruction.setPrevious(null);
    if (last == null) {
      first = instruction;
      last = instruction;
    } else {
      last.setNext(instruction);
      instruction.setPrevious(last);
      last = instruction;
    }
    instruction.setIndex(size++);
    array = null;
  }

  public InstructionHandle get(int index) {
    if (array == null) {
      array = toArray();
    }
    return array[index];
  }

  public int size() {
    return size;
  }

  public boolean isEmpty() {
    return size == 0;
  }

  public InstructionHandle[] toArray() {
    InstructionHandle[] result = new InstructionHandle[size];
    int i = 0;
    InstructionHandle current = first;
    while (current != null) {
      result[i++] = current;
      current = current.getNext();
    }
    return result;
  }

  public Iterator<InstructionHandle> iterator() {
    return new Iterator<InstructionHandle>() {
      private InstructionHandle current = first;

      public boolean hasNext() {
        return current != null;
      }

      public InstructionHandle next() {
        InstructionHandle next = current;
        current = current.getNext();
        return next;
      }

      public void remove() {
        throw new UnsupportedOperationException();
      }
    };
  }

  public void accept(InstructionVisitor visitor) {
    InstructionHandle current = first;
    while (current != null) {
      current.accept(visitor);
      current = current.getNext();
    }
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append('[');
    InstructionHandle current = first;
    while (current != null) {
      if (current != first) {
        sb.append(", ");
      }
      sb.append(current);
      current = current.getNext();
    }
    sb.append(']');

    return sb.toString();
  }
}

/*
 * Created on 2005-05-17
 */
package umbra.instructions;
import java.util.LinkedList;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

/**
 * This is completely abstract class that contains some information
 * useful when the line is modified or BCEL structure is created.
 * Most details are implemented in subclasses.
 *
 * Methods of this class should operate on the {@ref ClassGen}
 * object which is located in the {@ref BytecodeDocument} object
 * that describes the state of the bytecode editor which contains
 * the line that corresponds to an object of the current class.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class BytecodeLineController {

  /**
   * The string representation of the bytecode line number.
   */
  protected String line;

  /**
   * The number of the method that contains the current line.
   * This is an index in the {@ref ClassGen} object in the
   * {@ref BytecodeDocument} object
   * that describes the state of the bytecode editor which contains
   * the line that corresponds to the current object.
   */
  protected int index;

  /**
   * TODO
   *
   * @param l the string representation of the line number.
   */
  public BytecodeLineController(final String l) {
    super();
    line = l;
  }

  /**
   * The method adds the link between the Umbra representation of
   * instructions to their representation in BCEL. In case the
   * line does not correspond to an instruction we only register
   * the number of the method the line is associated with.
   *
   * @param ih the BCEL instruction handle that corresponds to the
   *       instruction associated with the current object
   * @param il the list of instructions in the current method
   * @param mg the object which represents the method of the current
   *    instruction in the BCEL representation of the current class
   *    in the bytecode editor
   * @param i method number in the current class
   * @return true when the current line corresponds to an instruction, false
   *     otherwise
   */
  public boolean addHandle(final InstructionHandle ih,
               final InstructionList il,
               final MethodGen mg,
               final int i) {
    index = i;
    return false;
  }

  /**
   * This method is redefined in each subclass of particular
   * instruction type. It is used for creating a handle
   * containing appropriate BCEL instruction object
   * that matches with the instruction name.
   *
   * @return Handle to the appropriate instruction;
   *   null if the line is not an instruction one.
   */
  public Instruction getInstruction() {
    return null;
  }


  /**
   * TODO
   *
   * @param il
   * @param ins
   */
  public void setTarget(final InstructionList il, final Instruction ins) {

  }

  /**
   * TODO
   *
   * @param nextLine
   * @param cg a {@ref ClassGen} object in the {@ref BytecodeDocument} object
   *       that describes the state of the bytecode editor which contains
   *       the line that corresponds to the current object.
   * @param ins
   * @param metEnd
   * @param instructions
   * @param off
   */
  public void initHandle(final BytecodeLineController nextLine, final ClassGen cg,
      final Instruction ins, final boolean metEnd,
      final LinkedList instructions, final int off) {
  }

  /**
   * TODO
   *
   * @param oldLine
   * @param nextLine
   * @param cg a {@ref ClassGen} object in the {@ref BytecodeDocument} object
   *       that describes the state of the bytecode editor which contains
   *       the line that corresponds to the current object.
   * @param ins
   * @param metEnd
   * @param theLast
   * @param instructions
   * @param off
   */
  public void update(final BytecodeLineController oldLine,
             final BytecodeLineController nextLine,
             final ClassGen cg,
             final Instruction ins,
             final boolean metEnd, final boolean theLast,
             final LinkedList instructions, final int off) {
    if (oldLine.getHandle() != null) { //in case this was an instruction before
      oldLine.dispose(nextLine, cg, theLast, instructions, off);
    }
  }

  /**
   * TODO
   *
   * @return
   */
  public InstructionHandle getHandle() {
    return null;
  }

  /**
   * TODO
   *
   * @return
   */
  public InstructionList getList() {
    return null;
  }

  /**
   * TODO
   *
   * @return
   */
  public MethodGen getMethod() {
    return null;
  }

  /**
   * TODO
   *
   * @return
   */
  public final int getIndex() {
    return index;
  }



  /**
   * This method is used to check some basic condition of
   * correctness. For non-instruction line this is the only
   * checking. It is usually redefined in the subclasses so that
   * if it returns true the line is regarded to be correct.
   *
   * @return  true if the instruction is correct
   * @see    InstructionLineController#correct()
   */
  public boolean correct()  {
    return false;
  }

  /**
   * TODO
   *
   * @param nextLine
   * @param cg a {@ref ClassGen} object in the {@ref BytecodeDocument} object
   *       that describes the state of the bytecode editor which contains
   *       the line that corresponds to the current object.
   * @param theLast
   * @param instructions an array with instruction representations. These
   * are represented as objects the classes of which are subclasses of
   * {@ref InstructionLineController}.
   * @param off
   */
  public void dispose(final BytecodeLineController nextLine,
            final ClassGen cg,
            final boolean theLast,
            final LinkedList instructions, final int off) {
    System.out.println("dispose(BytecodeLineController)"+ ((InstructionLineController) (instructions.get(off))).getHandle().getInstruction().getName());
  }

  /**
   * TODO
   *
   * @param index2
   */
  public void setIndex(final int index2) {
    this.index = index2;
  }

  /**
   * The method returns the String representation of the current instruction
   * content.
   *
   * @return the representation of the line
   */
  public final String getLineContent() {
    return line;
  }
}

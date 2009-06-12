/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.TargetLostException;

import annot.bcclass.BCMethod;

import umbra.UmbraPlugin;
import umbra.instructions.InstructionParser;
import umbra.lib.UmbraException;

/**
 * This class defines a structure that describes a single byte code
 * instruction and contains related BCEL structures.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class InstructionLineController extends BytecodeLineController {


  /**
   * This array contains the classes which are able to handle lines with
   * mnemonics.
   */
  public static final Class [] INS_CLASS_HIERARCHY =  {
    ArithmeticInstruction.class,
    IConstInstruction.class,
    LoadStoreConstInstruction.class,
    LoadStoreArrayInstruction.class,
    ConversionInstruction.class,
    SingleInstruction.class,
    PushInstruction.class,
    JumpInstruction.class,
    IincInstruction.class,
    StackInstruction.class,
    ArrayInstruction.class,
    NewInstruction.class,
    FieldInstruction.class,
    InvokeInstruction.class,
    LdcInstruction.class,
    UnclassifiedInstruction.class};

  /**
   * The list of instructions in the method to which the current instruction
   * belongs.
   */
  private InstructionList my_instr_list;

  /**
   * A BCEL handle to the current instruction representation in BCEL
   * format.
   */
  private InstructionHandle my_instr_handle;

  /**
   * A BCEL object that represents the method in which the current instruction
   * is located.
   */
  private BCMethod my_methodgen;

  /**
   * The mnemonic name of the current instruction.
   */
  private String my_name;

  /**
   * The construction creates the controller which
   * binds the instruction mnemonic with the line text. The name is set locally
   * while the assignment of the line is done in the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @param a_name the mnemonic name of the instruction
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public /*@ pure @*/ InstructionLineController(final String a_line_text,
                                   final String a_name) {
    super(a_line_text);
    setName(a_name);
  }

  /**
   * This method returns the array of mnemonics handled by the current class.
   *
   * @return the array of the handled mnemonics
   */
  public static /*@ non_null @*/ String[] getMnemonics() {
    return new String[0];
  }

  /**
   * The method adds the link between the Umbra representation of
   * instructions to their representation in BCEL.
   *
   * @param a_handle the BCEL instruction handle that corresponds to the
   *       instruction associated with the current object
   * @param a_list the list of instructions in the current method
   * @param a_method_gen the object which represents the method of the current
   *    instruction in the BCEL representation of the current class
   *    in the byte code editor
   * @return always true as the subclasses of the current class correspond to
   *     instructions
   */
  public final boolean addHandle(final InstructionHandle a_handle,
               final InstructionList a_list,
               final BCMethod a_method_gen) {
    this.my_instr_handle = a_handle;
    this.my_instr_list = a_list;
    this.my_methodgen = a_method_gen;
    return true;
  }

  /**
   * The debugging method that prints out to the standard output the
   * information on the line given in the parameter. It prints out:
   * <ul>
   *   <li> the name of the instruction,</li>
   *   <li> the position of the instruction handle</li>
   * </ul>
   *
   *  @param a_line the line for which the information is printed out
   */
  public static void controlPrint(final BytecodeLineController a_line) {
    UmbraPlugin.messagelog("Init: next line");
    if (a_line == null)
      UmbraPlugin.messagelog("Null");
    else {
      final Instruction ins = a_line.getInstruction();
      if (ins == null)
        UmbraPlugin.messagelog("Null instruction");
      else
        UmbraPlugin.messagelog(ins.getName());
      if (a_line instanceof InstructionLineController) {
        final InstructionLineController new_line =
            (InstructionLineController) a_line;
        final InstructionHandle nih = new_line.getHandle();
        if (nih == null)
          UmbraPlugin.messagelog("Null handle");
        else
          UmbraPlugin.messagelog(Integer.toString(nih.getPosition()));
      } else {
        UmbraPlugin.messagelog("Non-instruction handle");
      }
    }
  }

  /**
   * This is a debugging helper method which prints out to the standard
   * output the contents of the given BCEL instruction list.
   *
   * @param an_ilist the instruction list to print out
   */
  public static void printInstructionList(final InstructionList an_ilist) {
    InstructionHandle ih = an_ilist.getStart();
    if (ih == null) {
      UmbraPlugin.messagelog("start my_instr_handle==null");
      return;
    }
    UmbraPlugin.messagelog(ih.getInstruction().getName());
    do {
      ih = ih.getNext();
      UmbraPlugin.messagelog(ih.getInstruction().getName());
    }
    while (ih != an_ilist.getEnd());
  }

  /**
   * Returns the {@link InstructionHandle} structure which corresponds to the
   * current instruction.
   *
   * @return the BCEL handle to the current instruction.
   */
  public final InstructionHandle getHandle() {
    return my_instr_handle;
  }

  /**
   * Returns the {@link InstructionList} structure in which the current
   * instruction is located.
   *
   * @return the BCEL list of the instructions of the method to which the
   *   current instruction belongs
   */
  public final InstructionList getList() {
    return my_instr_list;
  }

  /**
   * Returns the {@link BCMethod} structure responsible for the method in
   * which the instruction resides.
   *
   * @return the method in which the current instruction is located
   */
  public final BCMethod getMethod() {
    return my_methodgen;
  }

  /**
   * This method is redefined in each subclass. It is used
   * to check some basic condition of correctness. A positive
   * result is necessary to continue any attempt of
   * generating BCEL structures about the line.
   *
   * @return true if the instruction is correct
   */
  public boolean correct() {
    return true;
  }

  /**
   * @param a_name the mnemonic name to set
   */
  protected void setName(final String a_name) {
    my_name = a_name;
  }

  /**
   * Returns the name of the mnemonic.
   *
   * @return the name of the mnemonic
   */
  public String getName() {
    return my_name;
  }

  /*@
    @ ensures \result ==> getParser().isInitialised();
    @*/
  /**
   * This method parses initial part of a instruction line. This is a helper
   * method which parses the common part of each instruction line i.e.:
   *
   *  whitespace number : whitespace
   *
   * @return <code>true</code> when all the parsing is done sucessfully,
   *   <code>false</code> in case the initial portion of the line is not of
   *   the required form
   */
  protected boolean parseTillMnemonic() {
    boolean res = true;
    final InstructionParser parser = getParser();
    parser.resetParser();
    res = parser.swallowWhitespace();
    res = res && parser.swallowNumber(); //line number
    res = res && parser.swallowDelimiter(':'); // :
    res = res && parser.swallowWhitespace(); //whitespace before mnemonic
    return res;
  }

  /*@ requires my_methodgen != null;
    @
    @*/
  /**
   * This method replaces the current instruction handle in the method
   * generation structure with the one for the given instruction.
   *
   * First, we check if the given new line controller can give a proper
   * BCEL representation of an instruction. If it cannot, <code>false</code>
   * is returned. Next we check if the current instruction is the first one in
   * the method. Depending on that we insert the new instruction either at the
   * beginning of the method or after the instruction right before the
   * current one (respectively). In case the current instruction is a target of
   * some other instructions in the method, we re-target them to the new
   * instruction. At last, we delete the current instruction from the
   * instruction list of the current method.
   *
   * The current instruction line controller should not be used after the call
   * to this method as it is disconnected from the BCEL structures.
   *
   * @param a_newlc the instruction line which should replace the current one
   * @return <code>true</code> if the operation was carried out successfully,
   *   <code>false</code> otherwise
   */
  public boolean replace(final InstructionLineController a_newlc) {
    Instruction ins = a_newlc.getInstruction();
    if (ins == null) {
      ins = new NOP();
    }
    final BCMethod mg = getMethod();
    final InstructionList il = mg.getInstructions();
    final InstructionHandle prevIh = my_instr_handle.getPrev();
    final InstructionHandle newIh;
    if (prevIh != null)
      newIh = il.append(prevIh, ins);
    else
      newIh = il.insert(ins);
    a_newlc.addHandle(newIh, il, mg);
    if (my_instr_handle.hasTargeters()) {
      addTargeters(newIh, my_instr_handle, my_instr_handle.getTargeters());
      my_instr_handle.removeAllTargeters(); //il.delete does not perform this
    }
    try {
      il.delete(my_instr_handle);
    } catch (TargetLostException e) {
      UmbraPlugin.messagelog("IMPOSSIBLE: lost targets");
    }
    return true;
  }

  /**
   * This method adds given {@link InstructionTargeter} objects to the
   * given instruction.
   *
   * @param an_nins the {@link InstructionHandle} to add the targeters to
   * @param an_oins the {@link InstructionHandle} to be replaced in targeters
   *   with the new one
   * @param the_trgtrs the array with targeters to add to the instruction
   */
  private static void addTargeters(
                   final /*@ non_null @*/ InstructionHandle an_nins,
                   final /*@ non_null @*/ InstructionHandle an_oins,
                   final /*@ non_null @*/ InstructionTargeter[] the_trgtrs) {
    for (int i = 0; i < the_trgtrs.length; i++) {
      an_nins.addTargeter(the_trgtrs[i]);
      the_trgtrs[i].updateTarget(an_oins, an_nins);
    }
  }

  /*@
    @ requires an_ino >= 0;
    @*/
  /**
   * This method adds to the current line controller the given method generation
   * structure ({@link BCMethod}) together with its instruction list and
   * a handle for the new instruction inserted on the given position
   * {@code an_ino}. All the instructions starting with the given number are
   * shifted one position further.
   *
   * @param a_methodgen the method generation structure to add to the controller
   * @param an_ino the instruction number in the instruction list starting with
   *   0 (zero)
   */
  public final void makeHandleForPosition(final BCMethod a_methodgen,
                        final int an_ino) {
    this.my_methodgen = a_methodgen;
    this.my_instr_list = a_methodgen.getInstructions();
    final Instruction ins = getInstruction();
    if (an_ino < my_instr_list.getInstructionHandles().length) {
      final InstructionHandle prevInstr =
        my_instr_list.getInstructionHandles()[an_ino];
      this.my_instr_handle = my_instr_list.insert(prevInstr, ins);
    } else {
      this.my_instr_handle =  my_instr_list.append(ins);
    }
  }

  /**
   * Removes the current instruction from the BCEL list of the instructions
   * in the method. This method checks if the retargeting is required and
   * then tries to find a good candidate for the new target. First, the
   * next instruction is tried. If there is no next instruction then the
   * previous one is used. After the new target is found, the method
   * is retargeted to jump to the new instruction. Finally, the instruction
   * is deleted. If the final deletion fails the method will throw an exception.
   *
   * @throws UmbraException in case the deletion failed
   */
  public void dispose() throws UmbraException {
    if (my_instr_handle.hasTargeters()) {
      final InstructionTargeter[] targeters = my_instr_handle.getTargeters();
      InstructionHandle candidate = my_instr_handle.getNext();
      if (candidate == null) {
        candidate = my_instr_handle.getPrev();
      }
      addTargeters(candidate, my_instr_handle, targeters);
      my_instr_handle.removeAllTargeters();
    }
    try {
      my_instr_list.delete(getHandle());
    } catch (TargetLostException e) {
      throw new UmbraException();
    }
  }

  /**
   * This method returns the number of the instruction handled by the current
   * line controller. If no instruction can be associated with the line
   * the value -1 is returned.
   *
   * @return the number of the instruction or -1 in case the number cannot
   *   be determined
   */
  public int getNoInMethod() {
    final InstructionHandle[] ihs = getMethod().getInstructions().
                              getInstructionHandles();
    int res = -1;
    for (int i = 0; i < ihs.length; i++) {
      if (ihs[i] == getHandle()) {
        res = i;
      }
    }
    return res;
  }

  /**
   * Returns <code>true</code> when a BCEL method representation must be
   * associated with the current line controller. In case of the
   * {@link InstructionLineController} objects this always holds.
   *
   * @return <code>true</code> when a BCEL method representation must be
   *   associated with the current line controller, otherwise
   *   <code>false</code>
   */
  public boolean needsMg() {
    return true;
  }

  /**
   * Returns <code>true</code> when a BCEL method representation is
   * associated with the current line controller. As the instruction line
   * controllers may be associated with methods, this method returns the
   * information if the method is actually associated.
   *
   * @return <code>true</code> when a BCEL method representation is
   *   associated with the current line controller, otherwise <code>false</code>
   */
  public boolean hasMg() {
    return my_methodgen != null;
  }

  /**
   * Retruns the position of the current instruction in the byte code
   * array of the current method. This position may by not in sync with
   * the position in the textual representation. It is accurate only after
   * the setPosition is called on the instruction list of the current method.
   *
   * @return the position of the current instruction
   */
  public int getPC() {
    return my_instr_handle.getPosition();
  }
}

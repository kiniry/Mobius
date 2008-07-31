package annot.bcclass;

import java.util.Iterator;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import annot.attributes.AType;
import annot.attributes.BCAttributeMap;
import annot.attributes.InCodeAttribute;
import annot.attributes.MethodSpecification;
import annot.bcexpression.LocalVariable;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents a bytecode method.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BCMethod {

  /**
   * A flag to choose how bytecode should be displayed.
   * TODO: true -> ???, false -> ????
   */
  private static final boolean DISPLAY_STYLE = false;

  /**
   * Collection of all attributes inside method body.
   */
  private final BCAttributeMap amap;

  /**
   * BML class representation containing this method.
   */
  private final BCClass bcc;

  /**
   * Original (BCEL) method. Do not use any other methodGen's
   *     to manipulate byte code.
   */
  private final MethodGen bcelMethod;

  /**
   * Local variable array.
   */
  private final LocalVariable[] lvars;

  /**
   * Method specification attribute.
   */
  private MethodSpecification mspec;

  /**
   * Old local variable array.
   */
  private final LocalVariable[] oldvars;

  /**
   * A standard constructor from BCClass and MethodGen.
   *
   * @param abcc - BCClass containing this method,
   * @param m - BCEL's methodGen for this method.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCMethod(final BCClass abcc,
                  final MethodGen m)
    throws ReadAttributeException {
    MLog.putMsg(MessageLog.LEVEL_PINFO,
                "  initializing method: " + m.getName());
    this.bcc = abcc;
    this.bcelMethod = m;
    this.amap = new BCAttributeMap(this);
    final LocalVariableGen[] lvgens = m.getLocalVariables();
    final int cnt = lvgens.length;
    this.lvars = new LocalVariable[cnt];
    this.oldvars = new LocalVariable[cnt];
    setLocalVariables(lvgens);
    readBMLAttributes(m);
  }

  /**
   * Examines the attributes of the given method and incorporates all the
   * BML related ones as appropriate subobjects of the current object.
   *
   * @param m method representation from which the attributes are read
   * @throws ReadAttributeException if an attribute's data doesn't represent
   *   correct attribute of attribute's name
   */
  private void readBMLAttributes(final MethodGen m)
    throws ReadAttributeException {
    final Attribute[] attrs = m.getAttributes();
    final AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        ar.readAttribute((Unknown) attrs[i]);
      }
    }
  }

  /**
   * The method fills in the local variables and old local variables tables
   * with the variables based on the values in the given array of local
   * variable generators. The method fills in the initial segments of the
   * tables. The size of the given array of local variables should be not
   * greater than the sizes of the local tables. If this is greater the
   * {@link IndexOutOfBoundsException} is thrown.
   *
   * @param lvgens the array of local variable generators
   */
  private void setLocalVariables(final LocalVariableGen[] lvgens) {
    final int cnt = lvgens.length;
    for (int i = 0; i  <  cnt; i++) {
      final String name = lvgens[i].getName();
      this.lvars[i] = new LocalVariable(false, this, i, name, lvgens[i]);
      this.oldvars[i] = new LocalVariable(true, this, i, name, lvgens[i]);
    }
  }

  /**
   * Adds an annotation to the BCMethod.
   *
   * @param ica - annotation to be added.
   */
  public void addAttribute(final InCodeAttribute ica) {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS,
                "adding attribute: " + ica.toString());
    this.amap.addAttribute(ica, ica.getMinor());
  }

  /**
   * Computes instructions pc numbers (for all instructions)
   * and searches for instruction of given PC number.
   *
   * @param pc - offset (program counter) of an instruction.
   * @return instruction of given offset (from this method)
   *     or null if there is no such instruction.
   */
  public InstructionHandle findAtPC(final int pc) {
    final InstructionList il = getInstructions();
    il.setPositions();
    final Iterator iter = il.iterator();
    while (iter.hasNext()) {
      final InstructionHandle ih = (InstructionHandle) iter.next();
      if (ih.getPosition() == pc) {
        return ih;
      }
    }
    return null;
  }

  /**
   * Seraches for local variable of given name.
   * WARNING: Results may be undetermined if there are
   * many local variables of the same name in this method.
   *
   * @deprecated, use {@link #findLocalVariable(String, InstructionHandle)}
   *     instead.
   * @param name - name of local variable to look for.
   * @return (any) local variable of given name,
   *     or <code>null</code> if no variable could be found.
   */
  @Deprecated
  public LocalVariable findLocalVariable(final String name) {
    return findLocalVariable(name, null);
  }

  /**
   * Seraches for local variable of given name and range.
   *
   * @param name - name of local variable to look for,
   * @param startIH - instruction handle of first
   *     instruction in the method where this variable
   *     is visible.
   * @return local variable of given name,
   *     or <code>null</code> if no variable could be found.
   */
  public LocalVariable findLocalVariable(final String name,
                                         final InstructionHandle startIH) {
    for (int i = 0; i  <  this.lvars.length; i++) {
      if (this.lvars[i].getName().equals(name)) {
        if (startIH == null ||
            startIH == this.lvars[i].getBcelLvGen().getStart()) {
          return this.lvars[i];
        }
      }
    }
    return null;
  }

  /**
   * @return attribute map.
   */
  public BCAttributeMap getAmap() {
    return this.amap;
  }

  /**
   * @return BML class representation containing this method.
   */
  public BCClass getBcc() {
    return this.bcc;
  }

  /**
   * @return BCEL method generator. Use this instead of
   *     creating new on from BCEL Method.
   */
  public MethodGen getBcelMethod() {
    return this.bcelMethod;
  }

  /**
   * @return BCEL MethodGen's instructionList.
   */
  public InstructionList getInstructions() {
    return this.bcelMethod.getInstructionList();
  }

  /**
   * Returns local variable of given index.
   *
   * @param isOld - false, unless we need OLD(local variable)
   * @param index - number of local variable
   *     (in this method),
   * @return <code>index</code>-th local variable of this
   *     method.
   */
  public LocalVariable getLocalVariable(final boolean isOld, final int index) {
    if (isOld) {
      return this.oldvars[index];
    }
    return this.lvars[index];
  }

  /**
   * @return number of local variables.
   */
  public int getLocalVariableCount() {
    return this.lvars.length;
  }

  /**
   * @return method specification
   */
  public MethodSpecification getMspec() {
    return this.mspec;
  }

  /**
   * Refreshes the pc numbers for each bytecode instruction of
   * the current method and returns the current pc number of the instruction
   * for the given handle.
   *
   * @param ih the handle of the instruction to give pc number for
   * @return pc number of the instruction under the given handle
   */
  public int getPC(final InstructionHandle ih) {
    this.bcelMethod.getInstructionList().setPositions();
    return ih.getPosition();
  }

  /**
   * Displays method's bytecode with BML annotations.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of method's bytecode.
   */
  public String printCode(final BMLConfig conf) {
    String code = "";
    if (this.mspec != null) {
      code += this.mspec.printCode(conf);
    } else {
      code += "/*@\n  @\n  @*/\n";
    }
    code += toString();
    String bcode = "";
    if (DISPLAY_STYLE) {
      bcode = printCodeStyleTrue(conf);
    } else {
      bcode = printCodeStyleFalse(conf);
    }
    return code + bcode;
  }

  /**
   * The implementation of the representation style when {@link #DISPLAY_STYLE}
   * is <code>false</code>.
   *
   * @param conf the BML formulae display configuration to typesett the
   *   BML formulae
   * @return the string representation of the current method
   */
  private String printCodeStyleFalse(final BMLConfig conf) {
    final Method m = this.bcelMethod.getMethod();
    String bcode = "";
    if (!m.isAbstract()) {
      bcode = m.getCode().toString();
      bcode = bcode.substring(bcode.indexOf("\n") + 1);
      bcode = bcode.split("\n\n")[0];
      final String[] lines_in = bcode.split("\n");
      bcode = "";
      for (int l = 0; l  <  lines_in.length; l++) {
        final String line = lines_in[l];
        final int pc = Integer.parseInt(line.substring(0, line.indexOf(":")));
        String annotLines = "";
        final InCodeAttribute[] attrs = this.amap.getAllAt(findAtPC(pc))
            .getAll(AType.C_ALL);
        for (int i = 0; i  <  attrs.length; i++) {
          annotLines += attrs[i].printCode(conf);
        }
        bcode += Parsing.addComment(annotLines) + line + "\n";
      }
    }
    return bcode;
  }

  /**
   * The implementation of the representation style when {@link #DISPLAY_STYLE}
   * is <code>true</code>.
   *
   * @param conf the BML formulae display configuration to typesett the
   *   BML formulae
   * @return the string representation of the current method
   */
  private String printCodeStyleTrue(final BMLConfig conf) {
    final StringBuffer bcode = new StringBuffer("");
    final InstructionList il = this.bcelMethod.getInstructionList();
    il.setPositions();
    final Iterator iter = this.bcelMethod.getInstructionList().iterator();
    while (iter.hasNext()) {
      final InstructionHandle ih = (InstructionHandle) iter.next();
      bcode.append(this.amap.getAllAt(ih).printCode(conf));
      bcode.append(ih.getPosition()).append(": ").
            append(ih.getInstruction().
                      toString(this.bcc.getJC().getConstantPool())).
            append("\n");
    }
    return bcode.toString();
  }

  /**
   * Updates BCEL MethodGen's attributes and generates
   * BCEL's method.
   *
   * @return generated BCEL Method.
   */
  public Method save() {
    MLog.putMsg(MessageLog.LEVEL_PINFO, "  saving method: " +
                this.bcelMethod.getName());
    final AttributeWriter aw = new AttributeWriter(this);
    Attribute[] attrs = BCClass.removeBMLAttributes(this.bcelMethod
        .getAttributes());
    if (this.mspec != null) {
      attrs = BCClass.addAttribute(attrs, aw.writeAttribute(this.mspec));
    }
    if (this.amap.getLength()  >  0) {
      attrs = BCClass.addAttribute(attrs, aw
          .writeAttribute(this.amap.getAtab()));
      attrs = BCClass.addAttribute(attrs, aw.writeAttribute(this.amap
          .getLstab()));
    }
    this.bcelMethod.removeAttributes();
    for (int i = 0; i  <  attrs.length; i++) {
      this.bcelMethod.addAttribute(attrs[i]);
    }
    this.bcelMethod.update();
    this.bcelMethod.setMaxStack();
    this.bcelMethod.setMaxLocals();
    return this.bcelMethod.getMethod();
  }

  /**
   * Sets method specification attribute for this method.
   *
   * @param amspec - new method specification.
   */
  public void setMspec(final MethodSpecification amspec) {
    this.mspec = amspec;
  }

  /**
   * @return String representation of method's header.
   */
  @Override
  public String toString() {
    return this.bcelMethod.toString() + "\n";
  }

}

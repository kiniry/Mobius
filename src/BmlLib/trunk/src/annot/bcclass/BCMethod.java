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
   */
  private static final boolean displayStyle = false;

  /**
   * Collection of all attributes inside method body.
   */
  private final BCAttributeMap amap;

  /**
   * BCClass containing this method.
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
   * @param abcc - BCClass containig this method,
   * @param m - BCEL's methodGen for this method.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCMethod(final BCClass abcc, final MethodGen m)
    throws ReadAttributeException {
    MLog.putMsg(MessageLog.PInfo, "  initializing method: " + m.getName());
    this.bcc = abcc;
    this.bcelMethod = m;
    this.amap = new BCAttributeMap(this);
    final LocalVariableGen[] lvgens = m.getLocalVariables();
    final int cnt = lvgens.length;
    this.lvars = new LocalVariable[cnt];
    this.oldvars = new LocalVariable[cnt];
    for (int i = 0; i  <  cnt; i++) {
      final String name = lvgens[i].getName();
      this.lvars[i] = new LocalVariable(false, this, i, name, lvgens[i]);
      this.oldvars[i] = new LocalVariable(true, this, i, name, lvgens[i]);
    }
    final Attribute[] attrs = m.getAttributes();
    final AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        ar.readAttribute((Unknown) attrs[i]);
      }
    }
  }

  /**
   * Adds an annotation to the BCMethod.
   *
   * @param ica - annotation to be added.
   */
  public void addAttribute(final InCodeAttribute ica) {
    MLog.putMsg(MessageLog.PProgress, "adding attribute: " + ica.toString());
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
   * @return BCClass containing this method.
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
   * Computes pc numbers for each bytecode instruction of
   * a method containing this annotation and returns,
   * and returns pc number of instruction this annotation
   * is attached to.
   *
   * @return pc number of this annotation's
   *     bytecode instruction.
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
    if (displayStyle) {
      final InstructionList il = this.bcelMethod.getInstructionList();
      il.setPositions();
      final Iterator iter = this.bcelMethod.getInstructionList().iterator();
      while (iter.hasNext()) {
        final InstructionHandle ih = (InstructionHandle) iter.next();
        bcode += this.amap.getAllAt(ih).printCode(conf);
        bcode += ih.getPosition() + ": " + ih.getInstruction().toString(
                                                this.bcc.getJC()
                                                    .getConstantPool()) + "\n";
      }
    } else {
      final Method m = this.bcelMethod.getMethod();
      if (!m.isAbstract()) {
        bcode += m.getCode().toString();
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
    }
    return code + bcode;
  }

  /**
   * Updates BCEL MethodGen's attributes and generates
   * BCEL's method.
   *
   * @return generated BCEL Method.
   */
  public Method save() {
    MLog.putMsg(MessageLog.PInfo, "  saving method: " +
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
   * @param mspec - new method specification.
   */
  public void setMspec(final MethodSpecification mspec) {
    this.mspec = mspec;
  }

  /**
   * @return String representation of method's header.
   */
  @Override
  public String toString() {
    return this.bcelMethod.toString() + "\n";
  }

}

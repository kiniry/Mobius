/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.util.Iterator;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.classfile.Utility;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

import annot.attributes.AType;
import annot.attributes.method.InCodeAnnotation;
import annot.attributes.method.MethodSpecificationAttribute;
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
   * Collection of all the BML attributes inside the method body.
   */
  private BCAttributeMap amap;

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
   * Parameters array.
   */
  private final LocalVariable[] params;

  /**
   * Method specification attribute.
   */
  private MethodSpecificationAttribute mspec;

  /**
   * The boolean flag which indicates if the method is a constructor.
   */
  private boolean isConstructor;

  /**
   * A standard constructor from BCClass and MethodGen.
   *
   * @param abcc - BCClass containing this method,
   * @param m - BCEL's methodGen for this method.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCMethod(final BCClass abcc, final MethodGen m)
    throws ReadAttributeException {
    MLog.putMsg(MessageLog.LEVEL_PINFO, "  initializing method: " +
                m.getName());
    this.bcc = abcc;
    this.bcelMethod = m;
    this.amap = new BCAttributeMap(this);

    this.lvars = setLocalVariables(m);
    this.params = setParams(m.getArgumentTypes());
    this.isConstructor = m.getName().equals(Constants.CONSTRUCTOR_NAME);
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
    this.mspec = new MethodSpecificationAttribute(this);
    final Attribute[] attrs = m.getAttributes();
    final AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        ar.readAttribute((Unknown) attrs[i]);
      }
    }
  }

  /**
   * The method creates the local variables table with the variables based on
   * the values in the given array of local variable generators. The method
   * creates an array of the given length and fills in the initial segment of
   * it. This array handles the special case when the table with variable
   * generators is empty and method is an object method. It assumes then that
   * the local variables table should contain the representation of this.
   *
   * @param meth the method for which the local variables should be generated
   * @return the array with local variables
   */
  private LocalVariable[] setLocalVariables(final MethodGen meth) {
    final LocalVariableGen[] lvgens = meth.getLocalVariables();
    final int cnt = lvgens.length;
    LocalVariable[] res = new LocalVariable[lvgens.length];
    if (cnt == 0 && !bcelMethod.isStatic()) {
      res = new LocalVariable[1];
      final ClassGen jc = bcc.getBCELClass();
      final String typename = "L" + jc.getClassName() + ";";
      final Type t = Type.getType(typename);
      res[0] = new LocalVariable(this, 0, "this",
        new LocalVariableGen(0, "this", t, null, null));
      return res;
    }
    for (int i = 0; i  <  cnt; i++) {
      final String name = lvgens[i].getName();
      res[i] = new LocalVariable(this, i, name, lvgens[i]);
    }
    return res;
  }

  /**
   * The method fills in the parameter table with the variables based on the
   * values in the given array of variable types. The method fills in the
   * initial segments of the table. The size of the given array of parameters
   * should be not greater than the sizes of the local table. If this is greater
   * the {@link IndexOutOfBoundsException} is thrown.
   *
   * @param paramsNames the array of parameter types
   * @return the array with the {@link LocalVariable} objects describing
   *   the parameters
   */
  private LocalVariable[] setParams(final Type[] paramsNames) {
    final LocalVariable[] res = new  LocalVariable[paramsNames.length];
    final int cnt = paramsNames.length;
    for (int i = 0; i  <  cnt; i++) {
      String name;
      LocalVariableGen lvgen;
      if (lvars.length > 1) {
        name = lvars[i].getName();
        lvgen = lvars[i].getBcelLvGen();
      } else {
        name = null;
        lvgen = new LocalVariableGen(i + 1, null, paramsNames[i], null, null);
      }
      res[i] = new LocalVariable(this, i + 1, name, lvgen);
    }
    return res;
  }

  /**
   * Adds an annotation to the BCMethod.
   *
   * @param ica - annotation to be added.
   */
  public void addAttribute(final InCodeAnnotation ica) {
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
   * Searches for local variable of the given name which is visible
   * and range of instructions.
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
      if (this.lvars[i].getName() != null &&
          this.lvars[i].getName().equals(name)) {
        if (startIH == null ||
            startIH == this.lvars[i].getBcelLvGen().getStart()) {
          return this.lvars[i];
        }
      } else if (this.lvars[i].getName() == name) {
        return this.lvars[i]; // no name => parameter
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
   * @param index - number of local variable
   *     (in this method),
   * @return <code>index</code>-th local variable of this
   *     method.
   */
  public LocalVariable getLocalVariable(final int index) {
    LocalVariable res;
    if (lvars.length > 1) {
      res = this.lvars[index];
    } else if (index == 0) {
      res = this.lvars[0];
    } else {
      res = this.params[index - 1];
    }
    return res;
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
  public MethodSpecificationAttribute getMspec() {
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
    if (this.mspec.getSpecificationCases().size() > 0) {
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
        final InCodeAnnotation[] attrs = this.amap.getAllAt(findAtPC(pc))
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
                      toString(this.bcc.getBCELClass().getConstantPool().
                               getConstantPool())).
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
    if (this.mspec.getSpecificationCases().size() > 0) {
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
  public void setMspec(
      final MethodSpecificationAttribute /*@ non_null @*/ amspec) {
    this.mspec = amspec;
  }

  /**
   * Sets method's local specification table for this method.
   *
   * @param amspec - new method local specification table.
   */
  public void setMLocalSpecs(final BCAttributeMap amspec) {
    this.amap = amspec;
  }

  /**
   * @return String representation of method's header.
   */
  @Override
  public String toString() {
    return methodToString() + "\n";
  }

  /**
   * Return method content representation close to declaration format,
   * `public static void main(String[]) throws IOException', e.g.
   *
   * @return String representation of the method.
   */
  public final String methodToString() {
    final String access = Utility.accessToString(
      this.bcelMethod.getAccessFlags());
    String signature = Type.getMethodSignature(this.bcelMethod.getType(),
      this.bcelMethod.getArgumentTypes());

    signature = Utility.methodSignatureToString(signature,
      this.bcelMethod.getName(), access, true,
      this.bcelMethod.getLocalVariableTable(this.bcelMethod.getConstantPool()));

    final StringBuffer buf = new StringBuffer(signature);

    final String[] excs = this.bcelMethod.getExceptions();
    for (int i = 0; i < excs.length; i++) {
      buf.append("\n      throws " + excs[i].replace('.', '/'));
    }
    return buf.toString();
  }

  /**
   * Checks if the given index is a proper index of a local
   * variable in the current method. This method checks the local
   * variable table and in case this is not present it refers
   * to the number of parameters.
   *
   * @param i the index to check
   * @return <code>true</code> in case the index can be a local
   *   variable index, <code>false</code> otherwise
   */
  public boolean canBeLocalVariable(final int i) {
    if (lvars.length > 1) {
      return 0 <= i && i < lvars.length;
    }
    return i == 0 || (0 <= i - 1 &&  i - 1 < params.length);
  }

  /**
   * Returns <code>true</code> in case the method is a constructor.
   *
   * @return <code>true</code> in case the method is a constructor,
   *   <code>false</code> otherwise.
   */
  public boolean isConstructor() {
    return isConstructor;
  }


  public ConstantPoolGen getConstantPool() {
    return bcelMethod.getConstantPool();
  }


  public void setConstantPool(ConstantPoolGen ncpg) {
    bcelMethod.setConstantPool(ncpg);    
  }
}

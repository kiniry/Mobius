/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.SourceFile;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.ExceptionTable;
import org.apache.bcel.classfile.PMGClass;
import org.apache.bcel.classfile.Signature;

import annot.bcclass.BCConstantPool;

import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CPLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.lib.FileNames;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraSyntaxException;

/**
 * This class encapsulates the structure of the instruction lines of the
 * {@link BytecodeController} and gives the external interface to them.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01

 */
public class BytecodeControllerInstructions
                extends BytecodeControllerContainer {

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@link InstructionLineController}.
   */
  private LinkedList my_instructions;


  /**
   * The constructor does only the initialisation of the superclass. It does
   * no initalisation. The initialisation should be done in the
   * {@link #init(BytecodeDocument, String[], String[])} method.
   */
  public BytecodeControllerInstructions() {
    super();
  }

  /**
   * This method handles the initial parsing of a byte code textual document.
   * It creates a parser {@link InitParser} and runs it with the given
   * document and array with comments pertinent to the instruction lines.
   * Subsequently, it initialises the internal structures to handle editor
   * lines, instructions, comments, and modifications.
   *
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   * @param a_interline contains the texts of interline comments, the
   *   i-th entry contains the comment for the i-th line in the document,
   *   if this parameter is null then the array is not taken into account
   *   FIXME: currently ignored; https://mobius.ucd.ie/ticket/555
   * @return the string with the text of the document combined with the comments
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   * @throws UmbraMethodException thrown in case a method number has been
   *   reached which is outside the number of available methods in the document
   * @throws UmbraSyntaxException in case a syntax error in BML document is
   *   encountered
   */
  public String init(final BytecodeDocument a_doc,
                     final String[] a_comment_array,
                     final String[] a_interline)
    throws UmbraLocationException, UmbraMethodException, UmbraSyntaxException {
    // reset of mapping should be made here to switch constant pool parsing on
    getMapping().reset();
    final InitParser initParser = new InitParser(a_doc, a_comment_array,
                                                 a_interline);
    final String res = initParser.runParsing();
    super.init(initParser.getEditorLines());
    my_instructions = initParser.getInstructions();
    initComments(initParser, a_comment_array, a_interline);
    int a_methodnum = 0;
    if (!my_instructions.isEmpty()) {
      a_methodnum = ((BytecodeLineController)my_instructions.getLast()).
                  getMethodNo() + 1;
    }
    fillModTable(a_methodnum);
    initializeMapping(a_doc);
    if (FileNames.DEBUG_MODE) controlPrint(0);
    if (FileNames.CP_DEBUG_MODE) controlPrintCP(a_doc);
    return res;
  }

  /**
   * Initializes the mapping object (see {@link BytecodeMapping}).
   *
   * @param a_doc a bytecode document for which the mapping is set
   */
  public void initializeMapping(final BytecodeDocument a_doc) {
    getMapping().setClassNameIndex(a_doc.getJavaClass().getClassNameIndex());
    getMapping().
      setSuperclassNameIndex(a_doc.getJavaClass().getSuperclassNameIndex());
    final List < Attribute > attrs = new ArrayList < Attribute > ();
    for (Field f : a_doc.getJavaClass().getFields()) {
      getMapping().addFieldName(f, f.getNameIndex());
      getMapping().addFieldSignature(f, f.getSignatureIndex());
      for (Attribute a : f.getAttributes()) attrs.add(a);
    }
    for (Method m : a_doc.getJavaClass().getMethods()) {
      getMapping().addMethodName(m, m.getNameIndex());
      getMapping().addMethodSignature(m, m.getSignatureIndex());
      for (Attribute a : m.getAttributes()) {
        if (a instanceof Code) {
          final Code c = (Code) a;
          for (Attribute at : c.getAttributes()) attrs.add(at);
        }
        attrs.add(a);
      }
    }
    for (Attribute a : a_doc.getJavaClass().getAttributes()) attrs.add(a);
    for (Attribute a : attrs) {
      getMapping().addAttributeName(a, a.getNameIndex());
      if (a instanceof SourceFile) {
        getMapping().
          addAttributeSecondValue(a, ((SourceFile) a).getSourceFileIndex());
      } else if (a instanceof ConstantValue) {
        getMapping().
          addAttributeSecondValue(a,
                                  ((ConstantValue) a).getConstantValueIndex());
      } else if (a instanceof PMGClass) {
        final PMGClass p = (PMGClass) a;
        getMapping().addAttributeSecondValue(p, p.getPMGIndex());
        getMapping().addPMGClass(p, p.getPMGClassIndex());
      } else if (a instanceof Signature) {
        getMapping().
          addAttributeSecondValue(a, ((Signature) a).getSignatureIndex());
      } else if (a instanceof ExceptionTable) {
        final ExceptionTable e = (ExceptionTable) a;
        getMapping().addExceptionTable(e, e.getExceptionIndexTable());
      }
    }
    final List < LocalVariable > lvars =
      getMapping().getLocVars(a_doc.getJavaClass());
    for (LocalVariable lv : lvars) {
      getMapping().addLocVarNameIndex(lv, lv.getNameIndex());
      getMapping().addLocVarSignatureIndex(lv, lv.getSignatureIndex());
      getMapping().addLocVarName(lv, lv.getName());
      getMapping().addLocVarSignature(lv, lv.getSignature());
    }
  }

  /**
   * Prints BML constant pool representation of a constant pool in a given
   * bytecode document.
   *
   * @param a_doc a bytecode document contating constant pool which BML
   * representation is to be printed
   */
  public void controlPrintCP(final BytecodeDocument a_doc) {
    final BCConstantPool a_pool = a_doc.getBmlp().getBcc().getCp();
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Pool:");
    for (int i = 0; i < a_pool.getSize(); i++) {
      UmbraPlugin.messagelog(i + ": " + a_pool.getConstant(i));
    }
    UmbraPlugin.messagelog("Control print for methods:");
    for (int i = 0; i < a_doc.getJavaClass().getMethods().length; i++) {
      UmbraPlugin.messagelog("method " + i);
      for (int j = 0; j <
      a_doc.getJavaClass().getMethods()[i].getConstantPool().getLength(); j++) {
        UmbraPlugin.messagelog(j + ": " +
                           a_doc.getJavaClass().getMethods()[i].
                           getConstantPool().getConstant(j));
      }
    }
  }

  /**
   * Returns the line controller for the given instruction number.
   * The instruction number is the sequence number of the instruction in
   * the textual file.
   *
   * @param an_insno the number of the retrieved instruction
   * @return the controller line for the given instruction number
   */
  protected final InstructionLineController getInstruction(final int an_insno) {
    return (InstructionLineController)my_instructions.get(an_insno);
  }

  /**
   * Returns the total number of the instructions in the current document.
   *
   * @return the number of instructions in the current document
   */
  protected final int getNoOfInstructions() {
    return my_instructions.size();
  }


  /**
   * Finds the first instruction line controller in the given range of lines.
   *
   * @param the_first the first line to be checked
   * @param the_last the last line to be checked
   * @return the number of the line with the instruction line controller or -1
   *   in case there is no instruction line controller in the given range
   */
  protected final int getFirstInstructionInRegion(final int the_first,
                                                  final int the_last) {
    int first = -1;
    for (int i = the_first; i <= the_last; i++) {
      final BytecodeLineController o = getLineController(i);
      if (first < 0) {
        first = my_instructions.indexOf(o);
      }
      my_instructions.remove(o);
    }
    return first;
  }

  /**
   * Finds the first instruction line controller after the given point. The
   * line with the given number is included in the search.
   *
   * @param a_pos the position from which the search starts
   * @return the line number of the first position that is an instruction line,
   *   or -1 in case there is no instruction line after the given point
   */
  protected final int getFirstInstructionAfter(final int a_pos) {
    int first = -1;
    for (int i = a_pos + 1; i < getNoOfLines(); i++) {
      final BytecodeLineController o = getLineController(i);
      if (first < 0) {
        first = my_instructions.indexOf(o);
        if (first >= 0) break;
      }
    }
    return first;
  }

  /**
   * Adds the given list of instructions at the end of the local instruction
   * list.
   *
   * @param the_instructions the instructions to be added
   */
  protected final void appendInstructions(final LinkedList the_instructions) {
    my_instructions.addAll(the_instructions);
  }

  /**
   * Removes from the representation of the instructions the instructions
   * contained in the given region. The bounds of the region are included
   * in the removal operation. We assume that the <code>first</code> and
   * <code>the_last</code> are within the range of available line numbers.
   *
   * @param the_first the first line of the region
   * @param the_last the last line of the region
   */
  protected final void removeInstructionsInRegion(final int the_first,
                                                  final int the_last) {
    for (int i = the_first; i <= the_last; i++) {
      final BytecodeLineController blc = getLineController(i);
      my_instructions.remove(blc);
    }
  }

  /**
   * Insertst the given list of instructions at the given position. The
   * instructions after and including the postion <code>a_pos</code> are
   * shifted to the right (i.e. their indicies are increased) the number
   * of positions that is enough to cover the given list
   * <code>the_instructions</code>.
   *
   * @param a_pos the postion where the list is inserted
   * @param the_instructions the list to insert
   */
  protected final void insertInstructions(final int a_pos,
                                          final LinkedList the_instructions) {
    my_instructions.addAll(a_pos, the_instructions);
  }


  /**
   * This is a helper method used for debugging purposes. It prints out
   * all the instructions and editor lines in the internal Umbra
   * representation of a class file.
   *
   * @param an_index the number which allows to make different printouts
   */
  protected final void controlPrint(final int an_index) {
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of editor lines (" +
                           an_index + "):");
    for (int i = 0; i < getNoOfLines(); i++) {
      final BytecodeLineController line = getLineController(i);
      if (line == null) {
        UmbraPlugin.messagelog("null");
        return;
      }
      if (line instanceof CPLineController) {
        final CPLineController cplc = (CPLineController) line;
        UmbraPlugin.messagelog(line.getClass().getName() + ": " +
                               line.getLineContent() + ", BCEL entry: " +
                               cplc.getConstant().getClass().getName());
      } else {
        UmbraPlugin.messagelog(line.getClass().getName() +
                               ": " + line.getLineContent());
        if (!line.correct()) UmbraPlugin.messagelog("ABOVE INCORRECT");
      }
    }
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of bytecode modification (" +
                           an_index + "):");
    for (int i = 0; i < my_instructions.size(); i++) {
      final InstructionLineController line =
                            (InstructionLineController)my_instructions.get(i);
      if (line == null) {
        UmbraPlugin.messagelog("" + i + ". null");
        return;
      }
      //if (line.index == index) {
      UmbraPlugin.messagelog("" + i + ". " + line.getName());
      final InstructionHandle ih = line.getHandle();
      if (ih == null) UmbraPlugin.messagelog("  handle - null");
      else {
        UmbraPlugin.LOG.print("  handle(" + ih.getPosition() + ") ");
        final Instruction ins = ih.getInstruction();
        if (ins == null) UmbraPlugin.LOG.print("null instruction");
        else UmbraPlugin.LOG.print(ins.getName());
        if (ih.getNext() == null) UmbraPlugin.LOG.print(" next: null");
        else UmbraPlugin.LOG.print(" next: " + ih.getNext().getPosition());
        if (ih.getPrev() == null) UmbraPlugin.messagelog(" prev: null");
        else UmbraPlugin.messagelog(" prev: " + ih.getPrev().getPosition());
      }
      //}
    }
  }


  /*@ requires 0 <= the_first <= the_last <= my_editor_lines.size();
    @ requires (\forall int i; 0 <= i && i <= the_instructions.size();
    @           the_instructions.get(i) instanceof InstructionLineController);
    @ requires !the_instructions.constainsNull;
    @*/
  /**
   * This method replaces the instructions on the local instruction list
   * within the given range with the given new instructions.
   * The instructions that reside in the lines between {@code the_first}
   * and {@code the_last} inclusively are removed. Next all the instructions
   * in the {@code the_instructions} table are inserted in place corresponding
   * to the indicated range.
   *
   * @param the_first the first line to be replaced
   * @param the_last the last line to be replaced
   * @param the_instructions te instructions to be added to the representation
   */
  protected void replaceInstructions(final int the_first,
                                     final int the_last,
                                     final LinkedList the_instructions) {
    int first = getFirstInstructionInRegion(the_first, the_last);
    if (first < 0) { //there is not instruction in the given range
      first = getFirstInstructionAfter(the_last);
      if (first < 0) {
        appendInstructions(the_instructions);
        return;
      }
    } else {
      removeInstructionsInRegion(the_first, the_last);
      first = getFirstInstructionAfter(the_first);
      if (first < 0) {
        appendInstructions(the_instructions);
        return;
      }
    }
    insertInstructions(first, the_instructions);
  }


  /**
   * The method finds the {@link InstructionLineController} which is located
   * in the same method that the given position. We use here the strategy
   * to examine the lines after the given one until something different that
   * {@link EmptyLineController}, {@link AnnotationLineController}, or
   * {@link CommentLineController} is found. In case the first other line
   * found is an {@link InstructionLineController} we return that. Otherwise,
   * <code>null</code> is returned.
   *
   * @param the_editor_lines the list of lines which is seeked for the
   *   {@link InstructionLineController}
   * @param a_pos the position for which we try to find the line controller
   * @return the {@link InstructionLineController} which was found or
   *   <code>null</code> in case all the "empty" lines were examined and no
   *   instruction line was found
   */
  protected InstructionLineController getInstructionLineAround(
                        final LinkedList the_editor_lines,
                        final int a_pos) {
    int i = a_pos;
    while (the_editor_lines.get(i) instanceof EmptyLineController ||
           the_editor_lines.get(i) instanceof AnnotationLineController ||
           the_editor_lines.get(i) instanceof CommentLineController) {
      i++;
    }
    final Object o = the_editor_lines.get(i);
    if (o instanceof InstructionLineController) {
      return (InstructionLineController)o;
    }
    return null;
  }

}

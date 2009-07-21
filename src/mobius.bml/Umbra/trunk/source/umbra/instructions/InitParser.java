/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Iterator;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import annot.bcclass.BCMethod;

import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CPHeaderController;
import umbra.instructions.ast.CPLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.FieldLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraSyntaxException;

/**
 * This class handles the initial parsing of a byte code textual document.
 * It creates handlers for each line of the document and structures to handle
 * the end-of-line comments. It is also able to reconstruct the end-of-line
 * comments from the previous session (closed with the refresh action).
 *
 * This class is used by {@link BytecodeController} to initialise its internal
 * structures at the beginning of editing or after the refresh action is
 * performed.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class InitParser extends BytecodeCommentParser {


  /**
   * The byte code document to be parsed. It contains the corresponding BCEL
   * structures linked into it.
   */
  private BytecodeDocument my_doc;

  /**
   * This constructor initialises all the internal structures. It memorises
   * the given document and array with end-of-line comments. Furthermore,
   * it sets all the internal containers to be empty.
   *
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   * @param a_interline contains the texts of interline comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   */
  public InitParser(final BytecodeDocument a_doc,
                    final String[] a_comment_array,
                    final String[] a_interline) {
    super(a_comment_array, a_interline);
    my_doc = a_doc;
  }

  /**
   * Initialisation of all the byte code structures related to
   * the document; it uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@link BytecodeLineController})
   * together with the links to the BCEL objects. The comment
   * structures that might have come from previous sessions may cause changes
   * in the original textual representation. The method returns the changed
   * representation.
   *
   * The exact format is, according to BML Reference Manual, section 'Textual
   * Representation of Specifications':
   * <pre>
   *    classfile ::= fileheader typeheader typebody
   * </pre>
   *
   * This method initialises the parsing context, then it parses the header
   * of the class and then one by one parses the methods. At the end
   * the method initialises the structures to keep track of the modified
   * methods.
   * @return changed textual representation of the parsed class
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   * @throws UmbraMethodException thrown in case a method number has been
   *   reached which is outside the number of available methods in the document
   * @throws UmbraSyntaxException in case a syntax error in BML document is
   *   encountered
   */
  public final String runParsing()
    throws UmbraLocationException, UmbraMethodException, UmbraSyntaxException {
    initInstructionNo();
    int a_line_no = 0;
    final LineContext ctxt = new LineContext();
    a_line_no = swallowClassHeader(a_line_no, ctxt); //fileheader typeheader
    a_line_no = swallowTypeBody(a_line_no, ctxt); //typebody
    final String str = getNewContent();
    return str;
  }

  /**
   * The method parses the portion of a byte code text which is the content
   * of the type declaration.
   * The exact format is, according to "BML Reference Manual", section "Textual
   * Representation of Specifications":
   * <pre>
   *    typebody ::= [ staticsection ] [ objectsection ] constructors
   *                 [ methods ]
   * </pre>
   * @param a_line_no the line from which we start the parsing
   * @param a_ctxt the parsing context
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   * @throws UmbraMethodException thrown in case a method number has been
   *   reached which is outside the number of available methods in the document
   *
   */
  private int swallowTypeBody(final int a_line_no,
                              final LineContext a_ctxt)
    throws UmbraLocationException, UmbraMethodException {
    int line_no = a_line_no;
    line_no = swallowUpperSection(line_no, a_ctxt, true); //staticsection
    line_no = swallowUpperSection(line_no, a_ctxt, false); //objectsection
    a_ctxt.setMethodsToBeRead();
    line_no = swallowMethodsAndConstructors(line_no, a_ctxt); // constructors
                                                              // [ methods ]
    return line_no;
  }

  /**
   * The method parses the portion of a byte code text which contains the
   * declarations of constructors and methods.
   * The exact format is, according to "BML Reference Manual", section "Textual
   * Representation of Specifications":
   * <pre>
   *    allmethods ::= constructors [ methods ]
   *    constructors ::= constructor [ constructor ]...
   *    methods ::= [ method ]...
   * </pre>
   * Currently, we rely on the assumption that in a real class file constructors
   * come first and then methods so all the methods can be handled in the same
   * way.
   *
   * @param a_line_no the line from which we start the parsing
   * @param a_ctxt the parsing context
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   * @throws UmbraMethodException thrown in case a method number has been
   *   reached which is outside the number of available methods in the document
   */
  private int swallowMethodsAndConstructors(final int a_line_no,
                                            final LineContext a_ctxt)
    throws UmbraLocationException, UmbraMethodException {
    int line_no = a_line_no;
    int a_method_count = 0;
    while (line_no < my_doc.getNumberOfLines()) {
      a_ctxt.incMethodNo();
      updateAnnotations(a_ctxt);
      line_no = swallowMethod(line_no, a_method_count, a_ctxt);
      a_method_count++;
    }
    return 0;
  }

  /**
   * The method parses the portion of a byte code text which contains the
   * declarations of fields.
   * The exact format is, according to "BML Reference Manual", section "Textual
   * Representation of Specifications":
   * <pre>
   *    staticsection ::= [ staticfields ] [ staticspec ]
   * </pre>
   * or
   * <pre>
   *    objectsection ::= [ objectfields ] [ objectspec ]
   * </pre>
   * The upper version is chosen when a_isstatic is <code>true</code>.
   *
   * @param a_line_no the line from which we start the parsing
   * @param a_ctxt the parsing context
   * @param a_isstatic the flag which indicates if the upper section is static
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   */
  private int swallowUpperSection(final int a_line_no,
                                  final LineContext a_ctxt,
                                  final boolean a_isstatic)
    throws UmbraLocationException {

    a_ctxt.setFieldsToBeRead();
    return swallowFields(a_line_no, a_ctxt, a_isstatic); //no specs currently
  }

  /**
   * @param a_line_no the line from which we start the parsing
   * @param a_ctxt the parsing context
   * @param a_isstatic the flag which indicates if the upper section is static
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   */
  private int swallowFields(final int a_line_no,
                            final LineContext a_ctxt,
                            final boolean a_isstatic)
    throws UmbraLocationException {

    int res = a_line_no;
    while (res < my_doc.getNumberOfLines()) {
      final String a_linename = getLineFromDoc(my_doc, res, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(a_linename,
                                                           a_ctxt,
                                                           my_doc.getBmlp());
      if (!(lc instanceof FieldLineController) &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
      addEditorLine(lc);
      res++;
    }
    return res;
  }

  /**
   * The method parses the initial portion of a byte code text. This portion
   * contains the information about the class which the code implements.
   * The exact format is, according to BML Reference Manual, section 'Textual
   * Representation of Specifications':
   * <pre>
   *    header ::= fileheader typeheader
   *    fileheader ::= packageinfo constant-pools
   *    typeheader ::= classmodifiers class ident
   *                   [ class-extends-clause ] [ implements-clause ] nl...
   *                 | interfacemodifiers interface ident
   *                   [ interface-extends-clause ] [ implements-clause ] nl...
   *
   * </pre>
   * Note that whitespace may be comments as well.
   *
   * @param the_current_line the line from which we start the parsing (mostly 0)
   * @param a_ctxt the parsing context
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws UmbraLocationException in case one of the locations in the document
   *   was wrongly calculated
   * @throws UmbraSyntaxException in case a syntax error in BML document is
   *   encountered
   */
  private int swallowClassHeader(final int the_current_line,
                                 final LineContext a_ctxt)
    throws UmbraLocationException, UmbraSyntaxException {

    int j = the_current_line;
    String line = getLineFromDoc(my_doc, j, a_ctxt); //packageinfo
    a_ctxt.setInitial();
    BytecodeLineController lc = Preparsing.getType(line, a_ctxt,
                                                   my_doc.getBmlp());
    addEditorLine(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    j = swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines() - 1, a_ctxt);
                                                                  //empty lines
    j = swallowConstantPools(j, a_ctxt); //constant-pools
    j = swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines() - 1, a_ctxt);
                                                                  //empty lines
    line = getLineFromDoc(my_doc, j, a_ctxt); //typeheader
    lc = Preparsing.getType(line, a_ctxt, my_doc.getBmlp());
    addEditorLine(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    return swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines() - 1, a_ctxt);
  }

  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain a class pool. The method first swallows the header line of
   * a constant pool. Subsequently it parses line by line the given document
   * starting with the line after the header and tries to parse the lines and
   * associate them with constant pool entries. In case the first line is not
   * a constant pool header line the {@link UmbraSyntaxException} is
   * thrown. Then it tries to parse the second constant pool header and its
   * lines in the manner as the first constant pool.
   *
   * @param the_current_lno the line from which we start the parsing
   * @param a_ctxt the parsing context
   * @return the number of the first line after the constant pool
   * @throws UmbraLocationException in case a line number is reached which is
   *   not within the given document
   * @throws UmbraSyntaxException in case a syntax error in BML document is
   *   encountered
   */
  private int swallowConstantPools(final int the_current_lno,
                                   final LineContext a_ctxt)
    throws UmbraLocationException, UmbraSyntaxException {

    final String line = getLineFromDoc(my_doc, the_current_lno, a_ctxt);
    final BytecodeLineController lc = Preparsing.getType(line, a_ctxt,
                                                         my_doc.getBmlp());
    if (!(lc instanceof CPHeaderController)) {
      throw new UmbraSyntaxException(the_current_lno);
    }
    addEditorLine(the_current_lno, lc);
    a_ctxt.setInsideCP();
    int j = the_current_lno + 1;
    j = swallowCPContent(a_ctxt, j);
    j = swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines(), a_ctxt);
    final String dline = getLineFromDoc(my_doc, j, a_ctxt);
    final BytecodeLineController dlc = Preparsing.getType(dline, a_ctxt,
                                                          my_doc.getBmlp());
    if (dlc instanceof CPHeaderController) {
      final CPHeaderController lcc = (CPHeaderController)dlc;
      if (!lcc.getLineContent().startsWith(BytecodeStrings.
             JAVA_KEYWORDS[BytecodeStrings.SCP_KEYWORD_POS])) {
        throw new UmbraSyntaxException(the_current_lno);
      }
      addEditorLine(j, dlc);
      a_ctxt.setInsideCP();
      j = swallowCPContent(a_ctxt, ++j);
    }
    return j;
  }

  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain the content of a class pool. This method subsequently parses
   * line by line the given document starting with the given line number
   * and tries to parse the lines and associate them with constant pool entries.
   * In case the first line is not
   *
   * @param a_ctxt the parsing context
   * @param a_lineno the number of the first line to be parsed
   * @return the number of the first line after the constant pool
   * @throws UmbraLocationException in case a line number is reached which is
   *   not within the given document
   */
  private int swallowCPContent(final LineContext a_ctxt, final int a_lineno)
    throws UmbraLocationException {

    String line;
    int num = a_lineno;
    BytecodeLineController lc;
    while (num < my_doc.getNumberOfLines()) {
      line = getLineFromDoc(my_doc, num, a_ctxt);
      lc = Preparsing.getType(line, a_ctxt, my_doc.getBmlp());
      if (!(lc instanceof CPLineController)) {
        /* XXX (Umbra) it only works if all contant pool lines are
         * correct and not separated by empty lines (which should be true
         * when loaded from .class file) */
        break;
      }
      final CPLineController cplc = (CPLineController) lc;
      final int const_no = cplc.getConstantNumber();
      cplc.setConstant(my_doc.getBmlp().
                       getBcc().getCp().getConstant(const_no));
      addEditorLine(lc);
      num++;
    }
    return num;
  }

  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain a method. The method first swallows the eventual empty
   * lines before the method. Then the method checks if the method currently to
   * be parsed can fit into the structures within the BCEL representation.
   * Subsequently it parses line by line the given document starting with the
   * given line and tries to parse the lines and associate with them the
   * instructions from the BCEL structures. It assumes that the method starts
   * with a method header. The current method ends when an empty line is met or
   * when the end of the document is reached.
   *
   * @param the_line_no the line in the document starting with which the method
   *   parsing begins
   * @param a_method_no the number of the method to be parsed
   * @param a_ctxt a parsing context
   * @return the number of the first line after the method; it is the first
   *   line after the empty method delimiting line or the last line in the
   *   document in case the end of document is met
   * @throws UmbraLocationException in case a line number is reached which is
   *   not within the given document
   * @throws UmbraMethodException the given method number exceeds the range of
   *   available methods in the BCEL structure
   */
  private int swallowMethod(final int the_line_no,
                            final int a_method_no,
                            final LineContext a_ctxt)
    throws UmbraLocationException, UmbraMethodException {

    int j = swallowEmptyLines(my_doc, the_line_no,
                              my_doc.getNumberOfLines() - 1, a_ctxt);
    final BCMethod mg = getMethodGenFromDoc(my_doc, a_method_no);

    //swallow method header
    j = swallowMethodHeader(a_ctxt, j, mg);

    final InstructionList il = mg.getInstructions();
    if (il != null) {
      il.setPositions();
      final Iterator iter = il.iterator();

      for (; j < my_doc.getNumberOfLines(); j++) {
        final String  a_linename = getLineFromDoc(my_doc, j, a_ctxt);
        final BytecodeLineController lc =
          Preparsing.getType(a_linename, a_ctxt, my_doc.getBmlp());
        addEditorLine(j, lc);
        lc.setMethodNo(a_ctxt.getMethodNo());
        if (lc.isCommentStart()) { // ignore comments
          j = swallowEmptyLines(my_doc, ++j, my_doc.getNumberOfLines() - 1,
                                a_ctxt) - 1;
          continue;
        }
        if (lc instanceof EmptyLineController) { //method end
          return swallowEmptyLines(my_doc, ++j, my_doc.getNumberOfLines() - 1,
                                   a_ctxt);
        }
        if (lc instanceof InstructionLineController) { //instruction line
          handleleInstructionLine((InstructionLineController)lc, mg, il, iter);
        }
      }
    }
    return j;
  }

  /**
   * This method handles the parsing of the method header lines. It assumes that
   * the header contains the method signature and possibly the throws
   * declarations. The method finishes its work on the first non-throws
   * line of the document.
   *
   * @param a_ctxt the parsing context with which the parsing is done
   * @param a_lineno the line number of the first line to be parsed
   * @param a_methodgen the BMLLib method representation
   * @return the number of the first line that could not be parsed by this
   *   method
   * @throws UmbraLocationException in case a line number has been reached
   *   such that there is no such a line in the current document
   */
  private int swallowMethodHeader(final LineContext a_ctxt,
                                  final int a_lineno,
                                  final BCMethod a_methodgen)
    throws UmbraLocationException {

    int res = a_lineno;
    String a_linename = getLineFromDoc(my_doc, res, a_ctxt);
    BytecodeLineController lc = Preparsing.getType(a_linename, a_ctxt,
                                                   my_doc.getBmlp());
    addEditorLine(res, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    if (lc instanceof HeaderLineController) { // method header
      ((HeaderLineController)lc).setMethod(a_methodgen);
    }
    res++;
    for (a_linename = getLineFromDoc(my_doc, res, a_ctxt); true; res++) {
      lc = Preparsing.getType(a_linename, a_ctxt, my_doc.getBmlp());
      if (lc instanceof ThrowsLineController) { // method header
        addEditorLine(res, lc);
        lc.setMethodNo(a_ctxt.getMethodNo());
        a_linename = getLineFromDoc(my_doc, res + 1, a_ctxt);
      } else {
        break;
      }
    }
    return res;
  }

  /*@
    @ requires a_methgen.getInstructionList() == an_ilist;
    @*/
  /**
   * This method incorporates the given instruction line controller into the
   * internal structures and binds the controller with BCEL representation
   * of its instruction. The iterator {@code an_iter} iterates over the
   * instruction list {@code an_ilist} from the {@link MethodGen} object
   * in {@code a_methgen}. When the iterator has the next instruction this
   * instruction handle is associated with the given {@link BytecodeController}
   * object {@code a_lctrl} together with the given instruction list and
   * {@link MethodGen}. Except for that the method add the line controller
   * to the instructions structure and handles the comments for the line.
   *
   * @param a_lctrl the line controller which is handled
   * @param mg a BCEL representation of method in which the instruction
   *   lies
   * @param an_ilist an instruction list from the method above
   * @param an_iter the iterator in the instruction list above
   */
  private void handleleInstructionLine(final InstructionLineController a_lctrl,
                                       final BCMethod mg,
                                       final InstructionList an_ilist,
                                       final Iterator an_iter) {

    InstructionHandle ih = null;
    if (an_iter.hasNext())
      ih = (InstructionHandle)(an_iter.next());
    a_lctrl.addHandle(ih, an_ilist, mg);
    final int ino = addInstruction(a_lctrl);
    handleComments(a_lctrl, ino);
    incInstructionNo();

  }
}

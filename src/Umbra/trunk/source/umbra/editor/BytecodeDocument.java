/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.Document;
import org.eclipse.swt.widgets.Shell;

import umbra.instructions.BytecodeController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.lib.BMLParsing;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraSynchronisationException;
import annot.bcclass.BCClass;

/**
 * This class is an abstract model of a byte code document.
 * It mainly handles the synchronisation between a byte code file and a
 * Java source code file (in both directions).
 *
 * FIXME more detailed description
 * FIXME this class should not handle the showing of messages in case of
 *   exception
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeDocument extends Document {

  /**
   * For some unknown reason the document cannot be checked up
   * to the final line. The document should be checked only
   * up to length minus this constant.
   * TODO: this is weird
   */
  private static final int CHECK_ALL_LINES_DECREMENT = 2;


  /**
   * The Java source code editor for the source code file associated with
   * the current byte code document.
   */
  private CompilationUnitEditor my_related_editor;

  /**
   * The byte code editor that manipulates the current document.
   */
  private BytecodeEditor my_bcode_editor;

  /**
   * The object which contains the internal Umbra representation of the
   * current document.
   */
  private BytecodeController my_bcc;

  /**
   * This flag is <code>true</code> when the internal structures that connect
   * the text .btc file with the BCEL representation are initialised.
   */
  private boolean my_ready_flag; //@ initially false;

  /**
   * TODO.
   * Contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the file,
   *   if this parameter is null then the array is not taken into account
   */
  private String[] my_comment_array;

  private String[] my_interline;

  /**
   * BML-annotated byte code (text + AST) displayed in this
   * editor. All byte code modifications should be made
   * on this object.
   */
  private BMLParsing my_bmlp;

  private DocumentSynchroniser my_synchroniser;


  private boolean my_dirty;


  /**
   * It is true when the processing is inside the initialisation of the
   * document. This is to forbid double initialisation inside the init method.
   */
  private boolean my_is_in_init;


  public BytecodeDocument() {
    super();
    this.my_bcc = new BytecodeController();
  }

  /**
   * The Java source code editor of the source code file associated
   * with the current byte code document.
   *
   * @param an_editor updates the Java source code editor associated with the
   * current byte code document.
   */
  public final void setRelatedEditor(final CompilationUnitEditor an_editor) {
    my_related_editor = an_editor;
  }

  /**
   * @return the Java source code editor associated with the
   * current byte code document.
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return my_related_editor;
  }

  /**
   * @return the current representation of the Java class associated with
   * the document.
   */
  public final JavaClass getJavaClass() {
    return getBmlp().getBcc().getJC();
  }

  /**
   * The method returns the {@link ClassGen} object for the current
   * representation of the Java class file. Each time this method is called
   * a new object is generated.
   *
   * @return the current generator of the Java class file
   */
  public final ClassGen getClassGen() {
    return new ClassGen(getBmlp().getBcc().getJC());
  }

  /**
   * This method updates the byte code editor associated with the
   * current document. Additionally, it updates the fields that
   * represent the byte code of the document.
   *
   * @param an_editor the byte code editor
   * @param a_bmlp a BMLLib representation of the current class
   */
  public final void setEditor(final BytecodeEditor an_editor,
                              final BMLParsing a_bmlp) {
    my_bcode_editor = an_editor;
    an_editor.setDocument(this);
    if (a_bmlp != my_bmlp) {
      my_ready_flag = false;
      my_bmlp = a_bmlp;
    }
  }

  /**
   * @return the editor for the current byte code document
   */
  public final BytecodeEditor getEditor() {
    return my_bcode_editor;
  }

  /**
   * @return <code>true</code> when the document change listener has already
   * been added to the document
   */
  public final boolean isListenerAdded() {
    return !getDocumentListeners().isEmpty();
  }

  /**
   * @return a {@link String} table which represents byte code comments
   * associated with subsequent lines of the byte code file associated with
   * the current editor
   */
  public final String[] getEOLComments() {
    return my_bcc.getEOLComments();
  }

  /**
   * This method returns the interoperable representation of the multi-line
   * comments. The protocol is described in
   * {@link BytecodeController#getInterlineComments()}.
   *
   * @return array with multi-line comment strings
   */
  public final String[] getInterlineComments() {
    return my_bcc.getInterlineComments();
  }


  /**
   * @return boolean array, an entry is <code>true</code> whenever
   * the corresponding method is modified by the byte code editor
   */
  public final boolean[] getModified() {
    return my_bcc.getModified();
  }

  /**
   * Informs if the internal data structures that connection between
   * Umbra and BCEL is initialised.
   *
   * @return <code>true</code> when the structures are initialised,
   *   <code>false</code> otherwise
   */
  public boolean isReady() {
    return my_ready_flag;
  }

  /**
   * This method initialises the internal structures of the byte code
   * controller. In particular it initialises the object that
   * manages the BCEL operations and enables the relevant actions
   * in the Umbra plugin byte code contributor.
   *
   * TODO what's my_mod_table_flag
   */
  public void init() {
    try {
      final String str = my_bcc.init(this, my_comment_array, my_interline);
      my_ready_flag = true; //this causes the following line not to loop
      setTextWithDeadUpdate(str);
      my_bmlp.setCodeString(str);
    } catch (UmbraLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode initial parsing",
                                    "The current document has no positions" +
                                    " for line " +
                                    e.getWrongLocation());
    } catch (UmbraMethodException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode initial parsing",
                                    "The current document has too many" +
                                    " methods (" +
                                    e.getWrongMethodNumber() + ")");
    }
    //TODO why we decrease here by CHECK_ALL_LINES_DECREMENT?
    my_bcc.checkAllLines(0, getNumberOfLines() - CHECK_ALL_LINES_DECREMENT);
  }

  public void setModTable(final boolean[] the_modified) {
    my_bcc.setModified(the_modified);
  }

  /**
   * The method updates the internal structures of the document to reflect the
   * change. The change is already present in the textual representation of the
   * document.
   *
   * @param a_start the first changed line
   * @param an_oldend the last line of the change in the old version of the
   *   document
   * @param a_newend the last line of the change in the current version of the
   *   document
   * @throws UmbraException in case the change cannot be incorporated
   *   into the internal structures
   */
  public void updateFragment(final int a_start,
                             final int an_oldend,
                             final int a_newend)
    throws UmbraException {
    my_bcc.removeIncorrects(a_start, an_oldend);
    try {
      my_bcc.addAllLines(this, a_start, an_oldend, a_newend);
    } catch (UmbraLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode fragment parsing",
                        "The current document has no positions for a line " +
                        "after " + e.getWrongLocation());
    }
    my_bcc.checkAllLines(a_start, a_newend);
  }

  /**
   * Returns the information about the correctness of the current document.
   * It takes into account both the byte code mnemonics and the annotations.
   *
   * @return <code>true</code> when the document is syntactically correct, and
   *   <code>false</code> otherwise
   */
  public boolean allCorrect() {
    return my_bcc.allCorrect() && my_bmlp.isCorrect();
  }

  /**
   * Retruns the line number of the first instruction which contains error.
   *
   * @return the line number with the first error
   */
  public int getFirstError() {
    return my_bcc.getFirstError();
  }

  /**
   * TODO.
   * We must mark the document as not ready to reinit the internal structures
   * when the first edit occurs.
   *
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the file,
   *   if this parameter is null then the array is not taken into account
   * @param an_interline multi-line comments
   */
  public final void reinit(final String[] a_comment_array,
                           final String[] an_interline) {
    my_ready_flag = false;
    my_comment_array = a_comment_array;
    my_interline = an_interline;
    init();
  }

  /**
   * @return BML-annotated byte code (text + AST) displayed
   * in this editor. All byte code modifications should
   * be made on this object.
   *
   * @see BMLParsing
   */
  public BMLParsing getBmlp() {
    return my_bmlp;
  }

  /**
   * TODO responsible for changing the Bmllib structures based on the local
   * changed methods.
   */
  public void updateJavaClass() {
    if (BMLParsing.BMLLIB_ENABLED) {
      //XXX changed: obtaining JavaClass from my_bmlp field
      final BCClass bcc = getBmlp().getBcc();
      bcc.saveJC();
    }
  }

  /**
   * This method returns the textual representation of the byte code. The
   * textual representation is generated from the BMLlib structures.
   *
   * @return the textual representation of the byte code
   */
  public String printCode() {
    return getBmlp().getBcc().printCode();
  }

  /**
   * Highlights the area in the byte code editor which corresponds to the
   * marked position in the source code editor. Works correctly only when the
   * position {@code a_pos} is inside a method. We assume that the current
   * Java document is edited in the given Java editor.
   *
   * @param a_pos a position in the source code editor. Lines in related byte
   *   code editor containing the line with this postion will
   *   be highlighted
   * @throws UmbraLocationException UmbraLocationException in case a reference
   *   in a document is made to a position outside the document
   * @throws UmbraSynchronisationException  in case the sychronisation is
   *   scheduled for a position outside the method body
   * @throws JavaModelException
   */
  public void synchronizeSB(final int a_pos,
                            final CompilationUnitEditor an_editor)
    throws UmbraLocationException, UmbraSynchronisationException,
           JavaModelException {
    final DocumentSynchroniser synch = getDocSynch();
    synch.synchronizeSB(a_pos, an_editor);
  }

  private DocumentSynchroniser getDocSynch() {
    if (my_synchroniser == null) {
      my_synchroniser = new DocumentSynchroniser(this,
                              my_related_editor.getDocumentProvider().
                              getDocument(my_related_editor.getEditorInput()));
    }
    return my_synchroniser;
  }

  /**
   * Highlights the area in the source code editor which corresponds to
   * the marked area in the byte code editor. Works correctly only inside a
   * method body.
   *
   * @param a_pos index of line in byte code editor. Lines in related source
   *   code editor corresponding to this line will be highlighted.
   * @throws UmbraLocationException in case a position is reached in the
   *   source code or byte code editor which does not exists there
   * @throws UmbraSynchronisationException in case there is no instruction
   *   line which can be reasonably associated with the given position
   */
  public void synchronizeBS(final int a_pos)
    throws UmbraLocationException, UmbraSynchronisationException {
    final DocumentSynchroniser synch = getDocSynch();
    synch.synchronizeBS(a_pos);
  }

  /**
   * This method causes the initialisation of the structures which keep track
   * of the modified methods.
   */
  public void initModTable() {
    my_bcc.initModTable();
  }

  /**
   * Returns the {@link MethodGen} structure which handles the modifications
   * in the method of the given number.
   *
   * @param a_method_no the number of the method to be returned
   * @return the BCEL structure which handles the editing of the given method
   * @throws UmbraMethodException thrown in case the given method number
   *   is outside the range of available methods
   */
  public MethodGen getMethodGen(final int a_method_no)
    throws UmbraMethodException {
    try {
      return my_bmlp.getBcc().getMethod(a_method_no).getBcelMethod();
    } catch (IndexOutOfBoundsException e) {
      throw new UmbraMethodException(a_method_no);
    }
  }

  /**
   * This method checks if the current document is in the initialisation process
   * so that the changes of its content should not be processed.
   *
   * @return <code>true</code> when the document is in the initialisation
   *   process, <code>false</code> otherwise
   */
  public boolean isInInit() {
    return my_is_in_init;
  }

  /**
   * This method changes the content of this document in such a way that
   * the update of the internal structures is not done. This is used when
   * the initial structure is generated.
   *
   * @param a_string the text of the document
   */
  public void setTextWithDeadUpdate(final String a_string) {
    my_is_in_init = true;
    set(a_string);
    my_is_in_init = false;
  }

  /**
   * Returns the information about the correctness of the method bodies in
   * the current document.
   *
   * @return <code>true</code> when the method bodies are syntactically correct
   *   and <code>false</code> otherwise
   */
  public boolean bodyCorrect() {
    return my_bcc.allCorrect();
  }

  /**
   * Returns the information about the correctness of the last edited annotation
   * in the current document.
   *
   * @return <code>true</code> when the last annotation is syntactically correct
   *   and <code>false</code> otherwise
   */
  public boolean annotCorrect() {
    return my_bmlp.isCorrect();
  }

  /**
   * Returns the error message for the last edited annotation in the current
   * document.
   *
   * @return <code>true</code> when the last annotation is syntactically correct
   *   and <code>false</code> otherwise
   */
  public String getAnnotError() {
    return my_bmlp.getErrorMsg();
  }

  public int getLineForPCInMethod(final int pc, final int a_mno) {
    return my_bcc.getLineForPCInMethod(pc, a_mno);
  }

  public int getLastLineInMethod(final int a_mno) {
    return my_bcc.getLastLineInMethod(a_mno);
  }

  public int getInstructionLineBelow(final int a_line_no)
    throws UmbraException {
    return my_bcc.getInstructionLineBelow(a_line_no);
  }

  public int getMethodForLine(final int lineno) {
    return my_bcc.getMethodForLine(lineno);
  }

  /**
   * This method gives the program counter for the given line. It gives the
   * correct number only in case the given line is indeed a line which
   * contains an instruction and in that case it returns the program
   * counter associated with its BCEL representation (not the label number
   * in the text of the document).
   *
   * @param a_lineno the number of the line to retrieve the program counter for
   * @return the program counter or -1 in case the program counter cannot
   *   be retrieved
   */
  public int getLabelForLine(final int a_lineno) {
    final BytecodeLineController blc = my_bcc.getLineController(a_lineno);
    if (blc instanceof InstructionLineController) {
      final InstructionLineController ilc = (InstructionLineController) blc;
      return ilc.getPC();
    }
    return -1;
  }

}

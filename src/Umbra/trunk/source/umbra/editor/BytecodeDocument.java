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
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.Document;
import org.eclipse.ui.IEditorPart;

import umbra.UmbraException;
import umbra.instructions.BytecodeController;
import annot.bcclass.BCClass;

/**
 * This class is an abstract model of a byte code document.
 * It mainly handles the synchronisation between a byte code file and a
 * Java source code file (in both directions).
 *
 * FIXME more detailed description
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
   * The representation of the Java class the content of which
   * we edit in the current document. The corresponding
   * class generator object is in the {@link #my_classgen}
   * field.
   */
  //private JavaClass my_javaclass;

  /**
   * The object to build Java classes. It is associated
   * with the {@link #my_javaclass} field.
   */
  //private ClassGen my_classgen;

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
   */
  private boolean my_mod_table_flag; //@ initially false;

  /**
   * This array keeps track of which methods in the class edited by the
   * byte code editor are modified. It contains <code>true</code> on i-th
   * position when the i-th method is modified.
   *
   * TODO it's not completely true, the my_modified in my_bcc is the actual
   * point
   */
  private boolean[] my_modified;

  /**
   * TODO
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
  public final String[] getCommentTab() {
    return my_bcc.getEOLComments();
  }

  /**
   * This method returns the interoperable representation of the multi-line
   * comments. The protocol is described in
   * {@link BytecodeController#getInterlineComments()}.
   *
   * @return array with multi-line comment strings
   */
  public final String[] getInterlineTab() {
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
    my_bcc = new BytecodeController();
    my_bcc.init(this, my_comment_array, my_interline);
    if (my_mod_table_flag) {
      my_bcc.setModified(my_modified);
      my_mod_table_flag = false;
    }
    //TODO why we decrease here by CHECK_ALL_LINES_DECREMENT?
    my_bcc.checkAllLines(0, getNumberOfLines() - CHECK_ALL_LINES_DECREMENT);
    my_ready_flag = true;
  }

  public void setModTable(final boolean[] the_modified) {
    my_modified = the_modified;
    my_mod_table_flag = true;
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
    final int methodno = my_bcc.getMethodForLine(a_start);
    final MethodGen mg = my_bcc.addAllLines(this, a_start, an_oldend, a_newend);
    replaceMethod(methodno, mg);
    my_bcc.checkAllLines(a_start, a_newend);
  }

  public boolean allCorrect() {
    return my_bcc.allCorrect();
  }

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
  }

  /**
   *
   * @param a_methodno
   * @param a_methodgen
   */
  public void replaceMethod(final int a_methodno,
                            final MethodGen a_methodgen) {
    my_modified[a_methodno] = true;
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
   * changed methods
   */
  public void updateJavaClass() {
    // TODO Auto-generated method stub
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
   * @param a_pos index of line in source code editor. Lines in related byte
   *       code editor corresponding  to this line will be highlighted
   * @param an_editor the source code editor
   */
  public void synchronizeSB(final int a_pos,
                            final IEditorPart an_editor) {
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
   */
  public void synchronizeBS(final int a_pos) {
    final DocumentSynchroniser synch = getDocSynch();
    synch.synchronizeBS(a_pos);
  }

  public void initModTable() {
    final Method[] ms = getBmlp().getBcc().getJC().getMethods();
    my_modified = new boolean[ms.length];
  }

  /**
   * Returns the {@link MethodGen} structure which handles the modifications
   * in the method of the given number.
   *
   * @param a_method_no the number of the method to be returned
   * @return the BCEL structure which handles the editing of the given method
   */
  public MethodGen getMethodGen(final int a_method_no) {
    return my_bmlp.getBcc().getMethod(a_method_no).getBcelMethod();
  }
}

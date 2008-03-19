/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import java.io.IOException;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

/**
 * This is the main class that defines the byte code editor.
 * It does so by subclassing {@link TextEditor}, which is a standard class
 * extended by each editor plugin.
 * Its additional features are attributes that describe
 * BCEL structures related to the edited byte code
 * such as {@link JavaClass}, to obtain particular instructions,
 * and {@link org.apache.bcel.generic.ClassGen}, to allow changes in BCEL.
 *
 * The input file for this editor is a .btc
 * ({@link UmbraHelper#BYTECODE_EXTENSION}) file which resides
 * alongside the corresponding .java ({@link UmbraHelper#JAVA_EXTENSION})
 * file. (Note that it is a different place from the place for .class,
 * {@link UmbraHelper#CLASS_EXTENSION}, files).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */

public class BytecodeEditor extends TextEditor {

  /**
   * The Java source code editor that corresponds to the current
   * byte code editor.
   */
  private CompilationUnitEditor my_related_editor;

  /**
   * This field contains the number of history items. This
   * field contains -1 when there are no active history
   * snapshots (i.e. the history is clear).
   */
  private int my_history_num = -1;

  /**
   * The byte code editor configuration manager associated with the current
   * editor.
   */
  private BytecodeConfiguration my_bconf;

  /**
   * Byte code document currently edited by the editor.
   */
  private BytecodeDocument my_current_doc;

  /**
   * This constructor creates the class and initialises the default
   * colour manager.
   */
  public BytecodeEditor() {
    super();
    my_bconf = new BytecodeConfiguration();
    setSourceViewerConfiguration(my_bconf);
    setDocumentProvider(new BytecodeDocumentProvider());
  }

  /**
   * Default function used while closing the current editor.
   */
  public final void dispose() {
    super.dispose();
  }

  /**
   * Returns the Java source code editor associated with the current byte code
   * editor.
   *
   * @return the Java source code editor that byte code text has been generated
   *   from
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return my_related_editor;
  }

  /**
   * This is a function executed directly after the initialisation
   * and it arranges the relation between the editor and its source code
   * counterpart.
   *
   * @param an_editor Java code editor with intended relation
   *   (used in particular during synchronisation)
   */
  public final void setRelation(final CompilationUnitEditor an_editor) {
    my_related_editor = an_editor;
    final BytecodeDocument doc = getDocument();
    ((BytecodeDocumentProvider)getDocumentProvider()).setRelation(an_editor,
                                      this, getEditorInput(),
                                      doc.getJavaClass(), doc.getBmlp());

  }

  /**
   * This method is run automatically while standard Eclipse
   * 'save' action is executed. Additionally, the current class file is saved
   * under the name with '_' at the beginning for the later use (see
   * {@link umbra.editor.actions.BytecodeRebuildAction} and
   * {@link umbra.editor.actions.BytecodeCombineAction}). Except
   * for that, the method updates structure {@link JavaClass} in BCEL and binary
   * files to make visible in the class file the changes made in the editor.
   *
   * @param a_progress_monitor not used
   * @see org.eclipse.ui.texteditor.AbstractTextEditor#doSave(IProgressMonitor)
   */
  public final void doSave(final IProgressMonitor a_progress_monitor) {
    final IDocumentProvider p = getDocumentProvider();
    if (p == null)
      return;
    if (p.isDeleted(getEditorInput())) {
      if (isSaveAsAllowed()) {
        /*
         * 1GEUSSR: ITPUI:ALL - User should never loose changes made in the
         *                editors.
         * Changed Behavior to make sure that if called inside a regular save
         * (because of deletion of input element) there is a way to report back
         * to the caller.
         */
        performSaveAs(a_progress_monitor);
      } else {
        final Shell shell = getSite().getShell();
        final String title = "Bytecode Editor";
        final String msg = "Save As action is not allowed";
        MessageDialog.openError(shell, title, msg);
      }

    } else {
      updateState(getEditorInput());
      validateState(getEditorInput());
      performSave(true, a_progress_monitor);
    }

    final IFile a_file_from = makeSpareCopy();
    if (a_file_from == null) return;
    try {
      final BytecodeDocument doc = getDocument();
      doc.updateJavaClass();
      final JavaClass jc = doc.getJavaClass();
      final String path3 = a_file_from.getLocation().toOSString();
      jc.dump(path3);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  /**
   * This method saves the the current class file under a special name. This
   * name consists of '_' followed by the original name. The files of this
   * kind are used in {@link BytecodeRebuildAction} and
   * {@link BytecodeCombineAction}.
   *
   * @return the IFile which points to the class file being edited by the
   *   current editor
   */
  private IFile makeSpareCopy() {
    final IPath edited_path = ((FileEditorInput)getEditorInput()).getFile().
                                                             getFullPath();
    final String fnameTo = UmbraHelper.getSavedClassFileNameForBTC(edited_path);
    IFile a_file_from;
    try {
      a_file_from = UmbraHelper.getClassFileFileFor(
               ((FileEditorInput)getEditorInput()).getFile(),
               this, UmbraHelper.BYTECODE_EXTENSION);
    } catch (JavaModelException e2) {
      MessageDialog.openError(new Shell(), "Bytecode",
                              "No classfile path set for the project");
      return null;
    }
    final IPath pathTo = new Path(fnameTo);
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IFile fileTo = workspace.getRoot().getFile(pathTo);
    try {
      if (!fileTo.exists())
        a_file_from.copy(pathTo, true, null);
    } catch (CoreException e1) {
      MessageDialog.openError(new Shell(), "Bytecode",
        "The file \"" + a_file_from.getName() + "\" cannot be copied to " +
        pathTo.toOSString());
      return null;
    }
    return a_file_from;
  }

  /**
   * This method loads in the content of the class file corresponding to the
   * given Java source code file. The method finds the class file corresponding
   * to the given Java source code file, loads it to BCEL and BMLlib structures
   * then it generates the .btc file with the textual representation of the
   * class file. The BCEL and BMLlib representation of the class file is
   * associated with the given document. Additionally, the comment information
   * from the previous session is connected to the document.
   *
   * @param a_path a workspace relative path to a Java class file
   * @param a_doc the byte code document for which the refresh operation is
   *   taken
   * @param the_comments  a table of end-of-line comments to be inserted
   * @param the_interline_comments  table of comments between instructions to be
   *   also inserted
   * @throws ClassNotFoundException the class corresponding to the Java source
   *   code file cannot be found
   * @throws CoreException the reasons for this exception include:
   *<ul>
   * <li> The location corresponding to the edited input
   *       in the local file system is occupied by a directory.</li>
   * <li> The workspace is not in sync with the location of the input
   *       in the local file system and <code>force </code> is
   *       <code>false</code>.</li>
   * <li> Resource changes are disallowed during certain types of resource
   *      change event notification. See <code>IResourceChangeEvent</code> for
   *      more details.</li>
   * <li> The file modification validator of the input disallowed the
   *      change.</li>
   * <li> The parent of this resource does not exist.</li>
   * <li> The project of this resource is not accessible.</li>
   * <li> The parent contains a resource of a different type
   *      at the same path as this resource.</li>
   * <li> The name of this resource is not valid (according to
   *    <code>IWorkspace.validateName</code>).</li>
   * </ul>
   */
  public final void refreshBytecode(final IPath a_path,
                final BytecodeDocument a_doc,
                final String[] the_comments,
                final String[] the_interline_comments)
    throws ClassNotFoundException, CoreException {
    final SyntheticRepository repository = getCurrentClassRepository();
    final JavaClass jc = loadJavaClass(a_path, repository);
    if (jc == null) return;
    repository.removeClass(jc);
    BCClass bcc;
    try {
      bcc = new BCClass(jc);
      final BMLParsing bmlp = new BMLParsing(bcc);
      a_doc.setEditor(this, bmlp); //refresh BCEL structures
      a_doc.setTextWithDeadUpdate(a_doc.printCode()); //this is where the
                                    //textual representation is generated
      a_doc.reinit(the_comments, the_interline_comments);
      final FileEditorInput input = (FileEditorInput)getEditorInput();
      getDocumentProvider().saveDocument(null, input, a_doc, true);
    } catch (ReadAttributeException e1) {
      MessageDialog.openError(new Shell(), "Bytecode",
                              "Cannot load the byte code from the file " +
                              jc.getFileName());
      e1.printStackTrace();
    }
  }

  /**
   * This method loads from the given Java class repository a class pointed out
   * by the given path.
   *
   * @param a_path a workspace relative path to the class file
   * @param a_repo the repository to load the class from
   * @return the BCEL {@link JavaClass} structure with the content of the class
   *   file
   */
  private JavaClass loadJavaClass(final IPath a_path,
                                  final SyntheticRepository a_repo) {
    final String tmp = a_path.removeFirstSegments(1).toOSString();
    final String clname = (tmp.substring(0, tmp.lastIndexOf(".")));
    if (UmbraHelper.DEBUG_MODE)
      UmbraPlugin.messagelog("We open class: " + clname);
    final JavaClass jc;
    try {
      jc = a_repo.loadClass(clname);
    } catch (ClassNotFoundException e) {
      MessageDialog.openError(new Shell(), "Bytecode",
                              "Cannot find the class " + clname + ".class");
      return null;
    }
    return jc;
  }

  /**
   * The method gives the repository where all the class files associated
   * with the current project are located.
   *
   * @return the repository of the class files
   * @throws JavaModelException if the output location for the current project
   *   does not exist
   */
  private SyntheticRepository getCurrentClassRepository()
    throws JavaModelException {
    //obtain the classpath for the classes
    final IProject project = ((FileEditorInput)my_related_editor.
        getEditorInput()).getFile().getProject();
    final IJavaProject jproject = JavaCore.create(project);
    final IPath outputloc = jproject.getOutputLocation().append("/-"); //bogus
    final String pathName = UmbraHelper.getPath(outputloc).
                                               removeLastSegments(1).
                                               addTrailingSeparator().
                                               toPortableString();
    final ClassPath cp = new ClassPath(pathName);
    return SyntheticRepository.getInstance(cp);
  }

  /**
   * Updating number of historical versions executed
   * after adding new version.
   *
   * @return current number of versions; -1 if limit has been reached
   */
  public final int newHistory() {
    if (my_history_num == UmbraHelper.MAX_HISTORY) return -1;
    my_history_num++;
    return my_history_num;
  }

  /**
   * Updating number of historical versions
   * when all of them are removed.
   */
  public final void clearHistory() {
    my_history_num = -1;
  }

  /**
   * @param a_doc document to associate with the current editor
   */
  public final void setDocument(final BytecodeDocument a_doc) {
    if (UmbraHelper.DEBUG_MODE)
      UmbraPlugin.messagelog("Document in editor: " + a_doc.toString());
    my_current_doc = a_doc;
  }

  /**
   * @return the currently edited document
   */
  public final BytecodeDocument getDocument() {
    return my_current_doc;
  }

  /**
   * @param a_related_editor the Java source code editor to associate with the
   *   current byte code editor
   */
  public void setRelatedEditor(final CompilationUnitEditor a_related_editor) {
    this.my_related_editor = a_related_editor;
  }

  /**
   * This method disposes the colour allocated from the system and then calls
   * the superclass finalisation.
   *
   * @throws Throwable in case something wrong happens in the superclass
   *    finalisation
   */
  protected void finalize() throws Throwable {
    //my_bconf.disposeColor();  //FIXME!! this instruction caused problems!
    super.finalize();
  }

  /**
   * This method creates new colouring configuration and associates this with
   * the current editor. A new document is always created with default gray
   * colouring mode. In case, we want to make use of the code colouring
   * functionality, we must change that mode into another one. This is done
   * with the help of this method which replaces the colouring logic with
   * a one which is created here.
   *
   * @param a_doc the document for which we change the colouring
   */
  public void renewConfiguration(final BytecodeDocument a_doc) {
    my_bconf = new BytecodeConfiguration();
    final SourceViewer sv = ((SourceViewer)getSourceViewer());
    sv.unconfigure();
    setSourceViewerConfiguration(my_bconf);
    sv.configure(my_bconf);
    //it is weird that this must be set by hand
    final IAnnotationModel am = sv.getAnnotationModel();
    if (am != null) am.connect(a_doc);
    sv.refresh();
  }
}

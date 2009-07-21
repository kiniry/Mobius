/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
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
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import annot.bcclass.BCClass;
import annot.bcio.ReadAttributeException;

/**
 * This is the main class that defines the bytecode editor.
 * It does so by subclassing {@ref TextEditor}, which is a standard class
 * extended by each editor plugin.
 * Its additional features are attributes that describe
 * BCEL structures related to the edited bytecode
 * such as {@ref JavaClass}, to obtain particular instructions,
 * and {@ref ClassGen}, to allow changes in BCEL.
 *
 * The input file for this editor is a .btc
 * ({@ref UmbraHelper#BYTECODE_EXTENSION}) file which resides
 * alongside the corresponding .java ({@ref UmbraHelper#JAVA_EXTENSION})
 * file. (Note that it is a different place from the place for .class,
 * {@ref UmbraHelper#CLASS_EXTENSION}, files).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */

public class BytecodeEditor extends TextEditor {

  /**
   * The Java source code editor that corresponds to the current
   * bytecode editor.
   */
  private CompilationUnitEditor my_related_editor;


  /**
   * The BCEL structure which represents the bytecode the content of the
   * current editor has been generated from. They also serve to modify
   * the bytecode.
   */
  private JavaClass my_javaclass;

  /**
   * The BCEL structure to generate the bytecode file corresponding
   * to the {@link #my_javaclass}.
   */
  private ClassGen my_classgen;

  /**
   * This field contains the number of history items. This
   * field contains -1 when there are no active history
   * snapshots (i.e. the history is clear).
   */
  private int my_history_num = -1;

  /**
   * The bytecode editor configuration manager associated with the current
   * editor.
   */
  private BytecodeConfiguration my_bconf;

  /**
   * Bytecode document edited by the editor.
   */
  private BytecodeDocument my_current_doc;

  /**
   * This constructor creates the class and initialises the default
   * color manager.
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
   * @return Java code editor that Bytecode has been generated from
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return my_related_editor;
  }

  /**
   * @return BCEL structure related to Bytecode
   * that allows obtaining its particular instructions
   */
  public final JavaClass getJavaClass() {
    return my_javaclass;
  }

  /**
   * This is a function executed directly after initialization
   * and it arranges the relation between the editor and BCEL structures.
   *
   * @param an_editor  Java code editor with intended relation
   *           (used in particular during synchronization)
   * @param a_javaclass    BCEL structures that Bytecode has been
   *           generated from and may be modificated with
   */
  public final void setRelation(final CompilationUnitEditor an_editor,
                                final JavaClass a_javaclass) {
    my_related_editor = an_editor;
    my_javaclass = a_javaclass;
    my_classgen = new ClassGen(a_javaclass);
    ((BytecodeDocumentProvider)getDocumentProvider()).
            setRelation(an_editor, this, getEditorInput());
  }

  /**
   * This method is run automatically while standard Eclipse
   * 'save' action is executed. Additionally to the usual
   * editor saving, it also updates structure JavaClass in BCEL
   * and binary files to allow Bytecode modifications being seen
   * while executing. The original binary file is saved with the name
   * with '_' at the beginning in case later rebuilding (if there has
   * not existed such yet, the binary file is simply rewritten, otherwise
   * it is saved unchanged).
   *
   * @param a_progress_monitor TODO
   * @see org.eclipse.ui.texteditor.AbstractTextEditor#doSave(IProgressMonitor)
   */
  public final void doSave(final IProgressMonitor a_progress_monitor) {
    super.doSave(a_progress_monitor);
    final IPath active = ((FileEditorInput)getEditorInput()).getFile().
                                                             getFullPath();
    final String fnameTo = UmbraHelper.getSavedClassFileNameForBTC(active);
    IFile a_filefrom;
    try {
      a_filefrom = UmbraHelper.getClassFileFileFor(
               ((FileEditorInput)getEditorInput()).getFile(),
               this, UmbraHelper.BYTECODE_EXTENSION);
    } catch (JavaModelException e2) {
      MessageDialog.openError(new Shell(), "Bytecode",
                              "No classfile path set for the project");
      return;
    }
    final IPath pathTo = new Path(fnameTo);
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IFile fileTo = workspace.getRoot().getFile(pathTo);
    try {
      if (!fileTo.exists())
        a_filefrom.copy(pathTo, true, null);
    } catch (CoreException e1) {
      e1.printStackTrace();
    }
    try {
      final JavaClass jc = my_classgen.getJavaClass();
      final String path3 = a_filefrom.getLocation().toOSString();
      jc.dump(path3);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  /**
   * Transform a relative file path (inside the project) into the absolute one.
   *
   * @param a_path a relative path
   * @return the corresponding absolute path
   */
  public final IPath getPath(final IPath a_path) {
    return ResourcesPlugin.getWorkspace().getRoot().getFolder(a_path).
                           getLocation();
  }

  /**
   * Generates input file from a {@link JavaClass} structure and puts it into
   * the editor window. The input file is created literally from the
   * {@link JavaClass} code getting methods.
   *
   * This method can also add to the displayed text the comments which were
   * added to the bytecode file before. They are displayed when they are given
   * as the parameters <code>the_comments</code> and
   * <code>the_interline_comments</code>.
   *
   * TODO probably obsolete:
   * There is temporary limit of 256 characters for method name
   * and 4096 characters for method code.
   *
   * @param a_path a workspace relative path to a Java source code file
   * @param the_comments  a table of comments to be inserted
   * @param the_interline_comments  Table of comments between instructions to be
   *    also inserted
   * @throws ClassNotFoundException the class corresponding to the Java source
   *         code file cannot be found
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
                final String[] the_comments,
                final String[] the_interline_comments)
    throws ClassNotFoundException, CoreException {

    //obtain the classpath for the classes
    final IProject project = ((FileEditorInput)my_related_editor.
        getEditorInput()).getFile().getProject();
    final IJavaProject jproject = JavaCore.create(project);
    final IPath outputloc = jproject.getOutputLocation().append("/A");
                                                                //bogus name
    final String pathName = getPath(outputloc).removeLastSegments(1).
                                               addTrailingSeparator().
                                               toPortableString();

    // Get class name together with its package name
    //FIXME there is a better way to obtain the name!!!
    final String tmp = a_path.removeFirstSegments(1).toOSString();
    final String clname = (tmp.substring(0, tmp.lastIndexOf(".")));

    final ClassPath cp = new ClassPath(pathName);
    final SyntheticRepository strin = SyntheticRepository.getInstance(cp);
    final JavaClass jc = strin.loadClass(clname);
    strin.removeClass(jc);
    //controlPrint(jc);
//    ClassGen cg = new ClassGen(jc);
//    String clname2 = cg.getClassName();
//    ConstantPoolGen cpg = cg.getConstantPool();
//    Method[] methods = jc.getMethods();
//    byte[][] names = new byte[methods.length][256];
//    byte[][] code = new byte[methods.length][4096];
//    int[] namesLen = new int[methods.length];
//    int[] codeLen = new int[methods.length];
//    int off = 0;
    BCClass bcc;
    try {
      bcc = new BCClass(jc);
      //this is where the textual representation is generated
      //FIXME we have to make sure it makes sense!!!
      final char[] bccode = bcc.printCode().toCharArray();
      final byte[] contents = new byte[bccode.length];
      //here a char array is transformed to byte array
      for (int i = 0; i < bccode.length; i++) {
        contents[i] = (byte) bccode[i];
      }
      final FileEditorInput input = (FileEditorInput)getEditorInput();
      final IFile file = input.getFile();
      final InputStream stream = new ByteArrayInputStream(contents);
      if (file.exists()) {
        file.setContents(stream, true, true, null);
      } else {
        file.create(stream, true, null);
      }
      try {
        stream.close();
      } catch (IOException e) {
        //This cannot happen.
        UmbraPlugin.messagelog("IMPOSSIBLE: Stream close generated exception " +
                               "in BytecodeEditor.refreshBytecode");
      }

    } catch (ReadAttributeException e1) {
      e1.printStackTrace();
    }

    my_javaclass = jc;
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
   * @return the object which generates the class file
   */
  public final ClassGen getClassGen() {
    return my_classgen;
  }

  /**
   * This method sets the internal BCEL structures which contain the
   * information oabout the Java class.
   *
   * @param a_javaclass the Java class representation
   */
  public final void setJavaClass(final JavaClass a_javaclass) {
    my_javaclass = a_javaclass;
    my_classgen = new ClassGen(a_javaclass);
  }

  /**
   * @param a_doc document to associate with the current editor
   */
  public final void setDocument(final BytecodeDocument a_doc) {
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
   *   current bytecode editor
   */
  public void setRelatedEditor(final CompilationUnitEditor a_related_editor) {
    this.my_related_editor = a_related_editor;
  }

  /**
   * This method disposes the color allocated from the system and then calls
   * the superclass finalization.
   *
   * @throws Throwable in case something wrong happens in the superclass
   *    finalization
   */
  protected void finalize() throws Throwable {
    my_bconf.disposeColor();
    super.finalize();
  }
}

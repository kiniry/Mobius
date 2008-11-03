/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import annot.io.ReadAttributeException;
import api.Jml2BmlAPI;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generation of a new related byte code file
 * in a new editor window. This action, in addition to the bytecode, generates
 * the BML specifications generated from JML specifications using Jml2Bml
 * compiler.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */

public class JMLCompile extends DisasBCEL {

  /**
   * The editor of a Java file for which the byte code file is
   * generated.
   */
  private CompilationUnitEditor my_editor;

  /**
   * Finds {@link org.apache.bcel.classfile.JavaClass} structure related to the
   * current Java source code. Generates new byte code from it and displays
   * it in a new byte code editor window.
   *
   * @param an_action see the IActionDelegate.run(IAction)
   * @see org.eclipse.ui.IActionDelegate#run(IAction)
   */
  public final void run(final IAction an_action) {
    if (checkInitialSavingConditions()) return;
    final Shell shell = my_editor.getSite().getShell();
    final IFile jFile = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IFile bFile;
    try {
      bFile = FileNames.getClassFileFile(jFile, my_editor);
    } catch (JavaModelException e) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                              GUIMessages.DISAS_MESSAGE_TITLE,
                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
      return;
    }
    try {
      compile(jFile, bFile);
      openBCodeEditorForJavaFile(jFile);
    } catch (IOException e) {
      MessageDialog.openError(shell,
        GUIMessages.DISAS_MESSAGE_TITLE,
        GUIMessages.substitute(GUIMessages.DISAS_SAVEFORSOURCE_PROBLEMS,
                               jFile.getLocation().toOSString()));
    } catch (JavaModelException e) {
      MessageDialog.openError(shell,
                                GUIMessages.DISAS_MESSAGE_TITLE,
                                GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
    } catch (PartInitException e) {
      MessageDialog.openError(shell,
                                GUIMessages.DISAS_MESSAGE_TITLE,
                                GUIMessages.DISAS_EDITOR_PROBLEMS);
    } catch (ClassNotFoundException e) {
      messageProblemsWithLoading(jFile.getLocation());
    } catch (ReadAttributeException e) {
      messageProblemsWithLoading(jFile.getLocation());
    }
  }

  /**
   * This method delegates the compilation of JML to the Jml2Bml compiler.
   *
   * @param a_jfile the file for the Java source code
   * @param a_bfile the corresponding file for the class file
   * @throws ClassNotFoundException in case the class for the given file
   *   cannot be found
   * @throws ReadAttributeException in case a BML attribute from the given class
   *   file cannot be found
   * @throws IOException in case the class file cannot be saved to the given
   *   location
   */
  private void compile(final IFile a_jfile, final IFile a_bfile)
    throws ClassNotFoundException, ReadAttributeException, IOException {
    String bname = a_bfile.getName();
    final IPath path = a_bfile.getLocation();
    bname = bname.substring(0, bname.lastIndexOf("."));
    final String bpath = path.removeLastSegments(1).toOSString();
    final String sourceFile = a_jfile.getLocation().toOSString();
    Jml2BmlAPI.compile(sourceFile, bpath, bname);
  }

}

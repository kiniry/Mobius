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

import jml2bml.plugin.Jml2BmlPlugin;
import jml2bml.plugin.NotTranslatedException;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import annot.io.ReadAttributeException;

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
 * @author Krzysztof Jakubczyk (kjk@mimuw.edu.pl)
 * @version a-01
 */

public class JMLCompile extends DisasBCEL {

  /**
   * Finds the file for the current Java source code and to the resulting
   * classfile and then compiles in the JML as BML into the classfile using
   * Jml2Bml compiler. The compiler assumes that the classfile already exists.
   * After the compilation completes the method will open the bytecode editor
   * using the relevant functionality inherited from {@link DisasBCEL}.
   *
   * @param an_action see the IActionDelegate.run(IAction)
   * @see org.eclipse.ui.IActionDelegate#run(IAction)
   */
  public final void run(final IAction an_action) {
    if (checkInitialSavingConditions()) return;
    final Shell shell = getEditor().getSite().getShell();
    final IFile jFile = ((FileEditorInput)getEditor().getEditorInput()).
      getFile();
    final IFile bFile;
    try {
      bFile = FileNames.getClassFileFile(jFile, getEditor());
    } catch (JavaModelException e) {
      MessageDialog.openError(shell,
                              GUIMessages.DISAS_MESSAGE_TITLE,
                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
      return;
    }
    try {
      Jml2BmlPlugin.getDefault().compile(jFile, bFile);
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
    } catch (NotTranslatedException e) {
      MessageDialog.openError(shell,
                              GUIMessages.DISAS_MESSAGE_TITLE,
                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
    }
  }
}

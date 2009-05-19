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
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IConsoleView;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
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
    MessageConsole console = findConsole("Jml2Bml console");
    console.clearConsole();
    MessageConsoleStream out = console.newMessageStream();
    
    IWorkbenchPage page = getEditor().getEditorSite().getPage();
    String id = IConsoleConstants.ID_CONSOLE_VIEW;
    IConsoleView view = null;
    try {
      view = (IConsoleView) page.showView(id);
    } catch (PartInitException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }
    view.display(console);
    
    if (checkInitialSavingConditions()) return;
    final Shell shell = getEditor().getSite().getShell();
    final IFile jFile = ((FileEditorInput)getEditor().getEditorInput()).
      getFile();
    final IFile bFile;
    
    IJavaProject project = FileNames.getJavaElement(getEditor()).getJavaProject();
//    project.getOutputLocation()
//    try {
//      bFile = FileNames.getClassFileFile(jFile, getEditor());
//    } catch (JavaModelException e) {
//      MessageDialog.openError(shell,
//                              GUIMessages.DISAS_MESSAGE_TITLE,
//                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
//      return;
//    }
    try {
      Jml2BmlPlugin.getDefault().compile(jFile, project, out);
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
      e.printStackTrace();
      MessageDialog.openError(shell,
                              GUIMessages.DISAS_MESSAGE_TITLE,
                              e.toString());
    }
  }
  
  private static MessageConsole findConsole(String name) {
    ConsolePlugin plugin = ConsolePlugin.getDefault();
    IConsoleManager conMan = plugin.getConsoleManager();
    IConsole[] existing = conMan.getConsoles();
    for (int i = 0; i < existing.length; i++)
       if (name.equals(existing[i].getName()))
          return (MessageConsole) existing[i];
    //no console found, so create a new one
    MessageConsole myConsole = new MessageConsole(name, null);
    conMan.addConsoles(new IConsole[]{myConsole});
    return myConsole;
 }
}

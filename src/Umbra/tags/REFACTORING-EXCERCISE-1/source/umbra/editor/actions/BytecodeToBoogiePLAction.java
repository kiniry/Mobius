/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.actions;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import b2bpl.Main;
import b2bpl.Project;

/**
 * This action is used to convert Java Bytecode into BoogiePL. The following JAR
 * packages are required: - b2bpl.jar - asm.jar
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BytecodeToBoogiePLAction implements IEditorActionDelegate {

  /**
   * The current bytecode my_editor for which the action takes place.
   */
  private IEditorPart my_editor;

  /**
   * TODO.
   * @param an_action TODO
   * @param a_target_editor TODO
   * @see IEditorActionDelegate#setActiveEditor(IAction, IEditorPart)
   */
  public final void setActiveEditor(final IAction an_action,
                final IEditorPart a_target_editor) {
    my_editor = a_target_editor;
  }

  /**
   * TODO.
   * @param an_action TODO
   * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
   */
  public final void run(final IAction an_action) {

    final IPath active = ((FileEditorInput)my_editor.getEditorInput()).
                            getFile().getFullPath();
    if (my_editor.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                    UmbraHelper.B2BPL_MESSAGE_TITLE,
                    UmbraHelper.B2BPL_SAVE_BYTECODE_FIRST);
      return;
    }
    final int lind = active.toPortableString().
                            lastIndexOf(UmbraHelper.BYTECODE_EXTENSION);
    if (lind == -1) {
      MessageDialog.openInformation(my_editor.getSite().getShell(),
                  UmbraHelper.B2BPL_MESSAGE_TITLE,
                  UmbraHelper.INVALID_EXTENSION.replace(UmbraHelper.SUBSTITUTE,
                       UmbraHelper.BYTECODE_EXTENSION));
    } else {
      // replaceClass(active);


      // my_editor.doSave(null);
      // IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      // IProject project = root.getProject("selectedProject name");
      // String entirePath = p.getLocation().toOSString();

      final IFile file = ((FileEditorInput)my_editor.getEditorInput()).
                                                     getFile();

      // String location = root.getLocation().toString();

      final String projectPath = file.getProject().getLocation().toOSString();
      final String bytecodePath = file.getLocation().toOSString();
      final String boogiePLPath = UmbraHelper.replaceLast(bytecodePath,
                     UmbraHelper.BYTECODE_EXTENSION,
                     UmbraHelper.BOOGIEPL_EXTENSION);
      final String javaPath   = UmbraHelper.replaceLast(bytecodePath,
                     UmbraHelper.BYTECODE_EXTENSION,
                     "" /* .class" */).
                   substring(projectPath.length() + 1).
                   replace('\\', '.');

      final List args = new ArrayList < String > ();
      args.add("-basedir"); args.add(projectPath);
      args.add("-o"); args.add(boogiePLPath);

      // TODO include all files of the current project
      final IPath path = file.getLocation().removeLastSegments(1);
      UmbraPlugin.messagelog("Looking for other classes in " +
                             path.toOSString());
      for (String a : getClassesInDirectory(path.toFile())) {
        if (a.endsWith(".class")) {
          args.add(javaPath.substring(0, javaPath.lastIndexOf('.')) + "." +
                   a.substring(0, a.lastIndexOf('.')));
        }
      }

      final String[] argsArray = (String[])args.toArray(
                                                  new String[args.size()]);

      // MessageDialog.openError(my_editor.getSite().getShell(),
      //                         "Bytecode", "B");

      try {
        final PrintWriter messageWriter = new PrintWriter(
                                            new FileOutputStream(boogiePLPath));
        final Project proj = Project.fromCommandLine(argsArray, messageWriter);
        final Main main = new Main(proj);
        main.compile();
      } catch (IOException ioex) {
        UmbraPlugin.messagelog(ioex.toString());
      }

      // -------------- Load .bpl file in my_editor
      // TODO: Create BoogiePL Editor

      loadBPLFile(active, lind);
    }
  }

  /**
   * TODO.
   * @param a_dir TODO
   * @return TODO
   */
  private String[] getClassesInDirectory(final File a_dir) {
    if (a_dir.isDirectory()) {
      final String[] children = a_dir.list();
      return children;
    }
    return null;
  }

  /**
   * TODO.
   *
   * @param an_active TODO
   * @param a_lind TODO
   */
  private void loadBPLFile(final IPath an_active, final int a_lind) {
    /*  FIXME not sure if it makes sense
      final String actlind = an_active.toOSString().substring(0, a_lind);
      final String fname = actlind + UmbraHelper.BOOGIEPL_EXTENSION;
      final IWorkspace workspace = ResourcesPlugin.getWorkspace();
      final IFile file = workspace.getRoot().getFile(new Path(fname));

     final FileEditorInput input = new FileEditorInput(file);
     try {

      IWorkbenchPage page = my_editor.getEditorSite().getPage();
      BoogiePLEditor bplEditor = (BytecodeEditor) page.openEditor(input,
          UmbraHelper.BOOGIEPL_EDITOR_CLASS, true);
      bplEditor.refreshBytecode(active, null, null);
      input = new FileEditorInput(file);
      JavaClass jc = bplEditor.getMy_javaClass();
      page.closeEditor(bplEditor, true);
      bplEditor = (BytecodeEditor) page.openEditor(input,
          UmbraHelper.BOOGIEPL_EDITOR_CLASS, true);
      bplEditor.setRelation(my_editor, jc);

    } catch (CoreException e) {
      e.printStackTrace();
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }*/
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action TODO
   * @param a_selection TODO
   * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

}

package umbra.editor.actions;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
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
   * The current bytecode editor for which the action takes place.
   */
  private IEditorPart editor;

  /**
   * TODO
   */
  public final void setActiveEditor(final IAction action,
                final IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * TODO
   */
  public final void run(final IAction action) {

    final IPath active = ((FileEditorInput)editor.getEditorInput()).
                            getFile().getFullPath();
    if (editor.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(editor.getSite().getShell(),
                    UmbraHelper.B2BPL_MESSAGE_TITLE,
                    UmbraHelper.B2BPL_SAVE_BYTECODE_FIRST);
      return;
    }
    final int lind = active.toOSString().lastIndexOf(UmbraHelper.BYTECODE_EXTENSION);
    if (lind == -1) {
      MessageDialog.openInformation(editor.getSite().getShell(),
                  UmbraHelper.B2BPL_MESSAGE_TITLE,
                  UmbraHelper.INVALID_EXTENSION.replace(UmbraHelper.SUBSTITUTE,
                       UmbraHelper.BYTECODE_EXTENSION));
    } else {
      // replaceClass(active);


      // editor.doSave(null);
      // IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      // IProject project = root.getProject("selectedProject name");
      // String entirePath = p.getLocation().toOSString();

      final IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();

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

      final List < String > args = new ArrayList < String > ();
      args.add("-basedir"); args.add(projectPath);
      args.add("-o"); args.add(boogiePLPath);

      // TODO include all files of the current project
      final IPath path = file.getLocation().removeLastSegments(1);
      System.out.println("Looking for other classes in " + path.toOSString());
      for (String a : getClassesInDirectory(path.toFile())) {
        if (a.endsWith(".class")) {
          args.add(javaPath.substring(0, javaPath.lastIndexOf('.')) + "." + a.substring(0, a.lastIndexOf('.')));
        }
      }

      final String[] argsArray = (String[])args.toArray(new String[args.size()]);

      // MessageDialog.openError(editor.getSite().getShell(), "Bytecode", "B");

      try {
        final PrintWriter messageWriter = new PrintWriter(new FileOutputStream(boogiePLPath));
        final Project proj = Project.fromCommandLine(argsArray, messageWriter);
        final Main main = new Main(proj);
        main.compile();
      } catch (IOException ioex) {
        System.out.println(ioex.toString());
      }

      // -------------- Load .bpl file in editor
      // TODO: Create BoogiePL Editor

      loadBPLFile(active, lind);
    }
  }

  private String[] getClassesInDirectory(final File dir) {
    if (dir.isDirectory()) {
      final String[] children = dir.list();
      return children;
    }
    return null;
  }

  /**
   * TODO
   *
   * @param active
   * @param lind
   */
  private void loadBPLFile(final IPath active, final int lind) {
    IFile file;
    final String actlind = active.toOSString().substring(0, lind);
    final String fname = actlind + UmbraHelper.BOOGIEPL_EXTENSION;
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    file = workspace.getRoot().getFile(new Path(fname));
    final FileEditorInput input = new FileEditorInput(file);
    /*  FIXME not sure if it makes sense
     * try {
      
      
      IWorkbenchPage page = editor.getEditorSite().getPage();
      BoogiePLEditor bplEditor = (BytecodeEditor) page.openEditor(input,
          UmbraHelper.BOOGIEPL_EDITOR_CLASS, true);
      bplEditor.refreshBytecode(active, null, null);
      input = new FileEditorInput(file);
      JavaClass jc = bplEditor.getMy_javaClass();
      page.closeEditor(bplEditor, true);
      bplEditor = (BytecodeEditor) page.openEditor(input,
          UmbraHelper.BOOGIEPL_EDITOR_CLASS, true);
      bplEditor.setRelation(editor, jc);
      
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
   */
  public void selectionChanged(final IAction action, final ISelection selection) { }

}

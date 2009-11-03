/*
 * This file is part of the Esc/Java plugin project. Copyright 2004 David R. Cok
 * 
 * Created on Aug 8, 2004
 */
package escjava.plugin;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import mobius.util.plugin.Log;
import mobius.util.plugin.Utils;
import mobius.util.plugin.ZipEditorInput;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.ITextEditor;


/**
 * @author David Cok
 */
public class WarningDeclarationsAction implements
    org.eclipse.ui.IEditorActionDelegate {

  /** Caches the value of the window, when informed of it. */
  private IWorkbenchWindow window;
  
  /** Cached value of the current selection. */
  private ISelection selection;

  /** {@inheritDoc} */
  public void setActiveEditor(final IAction action, 
                              final IEditorPart targetEditor) {
    //System.err.println("IACTION " + action.getClass() + " " + action);
    if (targetEditor != null && targetEditor.getSite() != null) {
      window = targetEditor.getSite().getWorkbenchWindow();
    }
  }

  /** {@inheritDoc} */
  public void run(final IAction action) {
    //System.err.println("RUNNING IACTION " + action.getClass() + " " +
    // action);
    run(getWindow(), selection);
  }

  /**
   * Open the file associated with the given selected markers,
   * highlighting the first one.
   * 
   * @param window
   * @param sel
   */
  public static void run(final IWorkbenchWindow window,
                         final ISelection sel) {
    final Shell shell = window.getShell();
    final List<IMarker> list = getMarkers(window, sel);
    if (list.isEmpty()) {
      Utils.showMessage(shell, "EscJava2 Checker", "No Markers selected");
    } 
    else if (list.size() > 1) {
      Utils.showMessage(shell, "EscJava2 Checker",
          "Multiple markers selected - operation applies only to one marker");
    }
    else {
      final IMarker m = (IMarker)list.get(0);
      try {
        final List<String> mlist = EscjavaMarker.getExtraInfo(m);
        if (mlist.isEmpty()) {
          Utils.showMessage(shell, "EscJava2 Checker",
              "No associated declarations");
        } 
        else if (mlist.size() == 1) {
          final String s = (String)mlist.iterator().next();
          openEditor(window, s);
        } 
        else {
          // Need to put up a choice - FIXME
          final Iterator<String> i = mlist.iterator();
          if (i.hasNext()) {
            i.next(); // skip the first one
          }
          while (i.hasNext()) {
            openEditor(window, (String)i.next());
          }
          // Do the first one last so it has focus
          final String s = (String)mlist.iterator().next();
          openEditor(window, s);
        }
      } 
      catch (Exception e) {
        Log.errorlog("Failed to get associated information from a marker", e);
        Utils.showMessage(shell, "EscJava2 Checker",
            "Failed to get associated information - see Error Log");
      }
    }
  }

  /**
   * TODO
   * 
   * @param selection
   * @return List of IMarker objects in selection
   */
  @SuppressWarnings("unchecked")
  public static List<IMarker> getMarkers(final IWorkbenchWindow window, 
                                         final ISelection selection) {
    final List<IMarker> list = new LinkedList<IMarker>();
    if (!selection.isEmpty()) {
      if (selection instanceof IStructuredSelection) {
        final IStructuredSelection structuredSelection = (IStructuredSelection)selection;
        for (final Iterator<Object> iter = (Iterator<Object>) structuredSelection.iterator(); 
             iter.hasNext();) {
          final Object element = iter.next();
          if (element instanceof IMarker) {
            list.add((IMarker)element);
          }
        }
      }
      else if (selection instanceof ITextSelection) {
        try {
          final IWorkbenchPage page = window.getActivePage();
          final IEditorPart editor = page.getActiveEditor();
          final IEditorInput input = editor.getEditorInput();
          final IResource res = (IResource)input.getAdapter(IResource.class);
          final IMarker[] markers = res.findMarkers(EscjavaMarker.ESCJAVA_MARKER_ID,
                                                    true, IResource.DEPTH_INFINITE);
          final ITextSelection tsel = (ITextSelection)selection;
          for (IMarker marker: markers) {
            //int charstart = markers[i].getAttribute(IMarker.CHAR_START,-1);
            final int line = marker.getAttribute(IMarker.LINE_NUMBER, -1);
            //System.err.println("MARKER " + line + " " + charstart);
            if (line == tsel.getStartLine() + 1) {
              list.add(marker);
            }
          }
        } 
        catch (Exception e) {
          // Just skip - likely this did not look like
          // a standard editor on a file resource with markers
        }
      } 
      else {
        if (Log.on) {
          Log.log("Unsupported selection in getMarkers: " + selection.getClass());
        }
      }
    }
    return list;
  }

  /**
   * Open an editor containing to explore the given file.
   * 
   * @param window the current workbench
   * @param name the name of the file
   * @throws CoreException if the initialization of the editor fails
   */
  public static void openEditor(final IWorkbenchWindow window, final String name) throws CoreException {
    String fname = name;
    int offset = -1;
    int line = -1;
    int k = fname.lastIndexOf(' ');
    if (k != -1) {
      offset = Integer.parseInt(fname.substring(k + 1));
      fname = fname.substring(0, k);
      k = fname.lastIndexOf(' ');
      if (k != -1) {
        line = Integer.parseInt(fname.substring(k + 1));
        fname = fname.substring(0, k);
      }
    }
    final IPath p = new Path(fname);
    final int jk = fname.indexOf(".jar:");
    final IWorkbenchPage page = window.getActivePage();
    if (jk == -1) { // if the file is not in a jar file
      final IFile file = Utils.getRoot().getFileForLocation(p);
      //System.err.println("FOUND " + files.length + " FOR " + p);
      if (line == -1) {
        IDE.openEditor(page, file);
      }
      else {
        final IMarker marker = file.createMarker(IMarker.TEXT);
        marker.setAttribute(IMarker.LINE_NUMBER, line);
        IDE.openEditor(page, marker);
        marker.delete();
      }
      return;
    } 
    else { // if the file is contained in a jarfile
      final String jarfile = fname.substring(0, jk + 4);
      fname = fname.substring(jk + 5);
      try {
        final IStorageEditorInput sei = new ZipEditorInput(jarfile, fname);
        final IEditorPart ep = IDE.openEditor(page, sei,
            "org.eclipse.jdt.ui.CompilationUnitEditor");
        if (ep instanceof ITextEditor) {
          ((ITextEditor)ep).selectAndReveal(offset - 1, 0);
        }
        return;
      }
      catch (IOException e) {
        // skip;
        // Go on to show the display message below
      }
    }
    // The file is not in the current project
    Utils.showMessage(window.getShell(), "Open Spec File",
        "The referenced declaration is not present in the current project." + 
        Utils.eol + (fname.length() < 60 ? fname : 
                     (fname.substring(0, 60) + Utils.eol + fname.substring(60))) + 
                     ", line " + line);

  }

  /** {@inheritDoc} */
  public void selectionChanged(final IAction action, final ISelection sel) {
    this.selection = sel;
  }


  protected IWorkbenchWindow getWindow() {
    return window;
  }
}

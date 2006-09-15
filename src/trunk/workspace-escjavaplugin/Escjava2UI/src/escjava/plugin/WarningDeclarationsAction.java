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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.ITextEditor;

import pluginlib.Log;
import pluginlib.Utils;
import pluginlib.ZipEditorInput;

/**
 * @author David Cok
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class WarningDeclarationsAction implements
    org.eclipse.ui.IEditorActionDelegate {

  /** Caches the value of the window, when informed of it. */
  protected IWorkbenchWindow window;

  /** Caches the value of the shell in which the window exists. */
  protected Shell shell = null;

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IEditorActionDelegate#setActiveEditor(org.eclipse.jface.action.IAction,
   *      org.eclipse.ui.IEditorPart)
   */
  public void setActiveEditor(IAction action, IEditorPart targetEditor) {
    //System.out.println("IACTION " + action.getClass() + " " + action);
    if (targetEditor != null && targetEditor.getSite() != null) {
      window = targetEditor.getSite().getWorkbenchWindow();
      shell = window == null ? null : window.getShell();
    }
  }

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
   */
  public void run(IAction action) {
    // TODO Auto-generated method stub
    //System.out.println("RUNNING IACTION " + action.getClass() + " " +
    // action);
    run(shell, window, selection);
  }

  /**
   * TODO
   * 
   * @param shell
   * @param window
   * @param selection
   */
  static public void run(Shell shell, IWorkbenchWindow window,
      ISelection selection) {
    List list = getMarkers(window,selection);
    if (list.isEmpty()) {
      Utils.showMessage(shell, "EscJava2 Checker", "No Markers selected");
    } else if (list.size() > 1) {
      Utils.showMessage(shell, "EscJava2 Checker",
          "Multiple markers selected - operation applies only to one marker");
    } else {
      IMarker m = (IMarker)list.get(0);
      try {
        List mlist = EscjavaMarker.getExtraInfo(m);
        if (mlist.isEmpty()) {
          Utils.showMessage(shell, "EscJava2 Checker",
              "No associated declarations");
        } else if (mlist.size() == 1) {
          String s = (String)mlist.iterator().next();
          openEditor(window, s);
        } else {
          // Need to put up a choice - FIXME
          Iterator i = mlist.iterator();
          if (i.hasNext()) i.next(); // skip the first one
          while (i.hasNext()) {
            openEditor(window, (String)i.next());
          }
          // Do the first one last so it has focus
          String s = (String)mlist.iterator().next();
          openEditor(window, s);
        }
      } catch (Exception e) {
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
  static public List getMarkers(IWorkbenchWindow window, ISelection selection) {
    List list = new LinkedList();
    if (!selection.isEmpty()) {
      if (selection instanceof IStructuredSelection) {
        IStructuredSelection structuredSelection = (IStructuredSelection)selection;
        for (Iterator iter = structuredSelection.iterator(); iter.hasNext();) {
          Object element = iter.next();
          if (element instanceof IMarker) {
            list.add(element);
          }
        }
      } else if (selection instanceof TextSelection) {
        try {
          IWorkbenchPage page = window.getActivePage();
          IEditorPart editor = page.getActiveEditor();
          IEditorInput input = editor.getEditorInput();
          IResource res = (IResource)input.getAdapter(IResource.class);
          IMarker[] markers = res.findMarkers(EscjavaMarker.ESCJAVA_MARKER_ID,true,IResource.DEPTH_INFINITE);
          TextSelection tsel = (TextSelection)selection;
          for (int i = 0; i<markers.length; ++i) {
            //int charstart = markers[i].getAttribute(IMarker.CHAR_START,-1);
            int line = markers[i].getAttribute(IMarker.LINE_NUMBER,-1);
            //System.out.println("MARKER " + line + " " + charstart);
            if (line == tsel.getStartLine()+1) list.add(markers[i]);
          }
        } catch (Exception e) {
          // Just skip - likely this did not look like
          // a standard editor on a file resource with markers
        }
      } else {
        if (Log.on)
            Log.log("Unsupported selection in getMarkers: "
                + selection.getClass());
      }
    }
    return list;
  }

  /**
   * TODO
   * 
   * @param window
   * @param s
   * @throws Exception
   */
  static public void openEditor(IWorkbenchWindow window, String s)
      throws Exception {
    int offset = -1;
    int line = -1;
    int k = s.lastIndexOf(' ');
    if (k != -1) {
      offset = Integer.parseInt(s.substring(k + 1));
      s = s.substring(0,k);
      k = s.lastIndexOf(' ');
      if (k != -1) {
        line = Integer.parseInt(s.substring(k + 1));
        s = s.substring(0,k);
      }
    }
    String fname = s.trim();
    IPath p = new Path(fname);
    int jk = fname.indexOf(".jar:");
    IWorkbenchPage page = window.getActivePage();
    if (jk == -1) {
      IFile[] files = Utils.getRoot().findFilesForLocation(p);
      //System.out.println("FOUND " + files.length + " FOR " + p);
      for (int j = 0; j < files.length; ++j) {
        if (line == -1)
          IDE.openEditor(page, files[j]);
        else {
          IMarker marker = files[j].createMarker(IMarker.TEXT);
          marker.setAttribute(IMarker.LINE_NUMBER, line);
          IDE.openEditor(page, marker);
          marker.delete();
        }
        return;
      }
    } else {
      String jarfile = fname.substring(0, jk + 4);
      fname = fname.substring(jk + 5);
      try {
        IStorageEditorInput sei = new ZipEditorInput(jarfile, fname);
        IEditorPart ep = IDE.openEditor(page, sei,
            "org.eclipse.jdt.ui.CompilationUnitEditor");
        if (ep instanceof ITextEditor) {
          ((ITextEditor)ep).selectAndReveal(offset-1,0);
        }
        return;
      } catch (IOException e) {
        // skip;
        // Go on to show the display message below
      }
    }
    // The file is not in the current project
    Utils.showMessage(window.getShell(), "Open Spec File",
        "The referenced declaration is not present in the current project."
            + Utils.eol
            + (fname.length() < 60 ? fname : (fname.substring(0, 60)
                + Utils.eol + fname.substring(60))) + ", line " + line);

  }

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction,
   *      org.eclipse.jface.viewers.ISelection)
   */
  public void selectionChanged(IAction action, ISelection selection) {
    this.selection = selection;
  }

  /** Cached value of the current selection */
  private ISelection selection = null;
}
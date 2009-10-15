/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 */
package escjava.plugin.actions;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import pluginlib.Log;
import pluginlib.Utils;

/**
 * This class and its subclasses are the classes
 * that respond to Menu actions.
 * 
 * @author David R. Cok
 *
 */
public abstract class EscjavaAction implements IObjectActionDelegate,
                    IWorkbenchWindowActionDelegate {

  /** Caches the value of the window, when informed of it. */
  protected IWorkbenchWindow window;
  
  /** The current selection. */
  protected ISelection selection;
  

  /** {@inheritDoc} */
  public final void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
    //System.out.println("SET ACTIVE PART");
  }
  
  /** {@inheritDoc} */
  public final void selectionChanged(final IAction action, final ISelection sel) {
    selection = sel;
    //System.out.println("SEL CHANGED " + selection.getClass());
  }

  /**
   * We can use this method to dispose of any system
   * resources we previously allocated.
   * @see IWorkbenchWindowActionDelegate#dispose
   */
  public void dispose() {
  }
  
  /**
   * We will cache window object in order to
   * be able to provide parent shell for the message dialog.
   * @param win The parent window
   * @see IWorkbenchWindowActionDelegate#init
   */
  public void init(final IWorkbenchWindow win) {
    this.window = win;
  }

  /**
   * Shows a message to the user; call this only for situations 
   * in which we are already running in the UI thread.
   * @param msg  The message to show
   */
  protected void showMessage(final String msg) {
    Utils.showMessageInUI(window.getShell(), "ESC/Java2 Operation", msg);
  }

  /** {@inheritDoc} */
  public void run(final IAction action) {
    // Called in response to a menu selection (or other command)
    // Either this or some of the component template routines
    // (iterator, start, doit, end) should be overridden for
    // individual menu items
    try {
      //if (useProjects()) {
//      if (true) {
      final Map<IJavaProject, Collection<IAdaptable>>  map = 
        Utils.sortByProject(Utils.getSelectedElements(selection, window));
      iterateByProject(map);
//      } 
//      else {
//        Map<IPackageFragmentRoot, Collection<IAdaptable>> map = 
//      Utils.sortByPackageFragmentRoot(Utils.getSelectedElements(selection,window));
//        iterateByPFR(map);      
//      }
//    } catch (JMLEclipseCancel e) {
//      throw e;  // FIXME - where does this get caught?
    } 
    catch (Exception e) {
      Log.errorlog("Exception occurred in executing a menu item action: ", e);
    }
  }

  /**
   * Iterates over all the projects in the map (as produced by
   * getJavaElements()), calling start/doit/end for each project's collection
   * of IJavaElements and IResources.  The order of iteration is that supplied by
   * orderedProjectsIterator(map).  The map must be indexed by project.
   * 
   * Expected to be called in the UI thread.
   * @param map The map containing IJavaProjects and their Collections of
   * IJavaElements and IResources.
   */
  public void iterateByProject(final Map<IJavaProject, Collection<IAdaptable>> map) {
    boolean nothing = true;
    final Iterator<IProject> ii = orderedProjectIterator(map);
    while (ii.hasNext()) {
      final IJavaProject jp = JavaCore.create(ii.next());
      final Collection<IAdaptable> elements = map.get(jp);
      if (Log.on) {
        Log.log("  Doing project " + jp.getElementName() + " " + elements.size() + " items");
      }
      if (!elements.isEmpty()) {
        nothing = false;
      }
      // Catch exceptions here so that we can continue on after an error
      // in one project to do other projects
      try {
        if (!start(jp, elements)) {
          continue;
        }
        for (IAdaptable o: elements) {
          final boolean ok = doit(o);
          if (!ok) {
            if (Log.on) {
              Log.log("Unable to process an item of type " + o.getClass());
            }
            showMessage("Unable to process an item of type " + o.getClass());
          }
        }
        end(jp, elements);
//      } catch (JMLEclipseCancel e) {
//        throw e;
      }
      catch (Exception e) {
        Log.errorlog("Exception occurred while processing project " + jp.getElementName(),e);
        showMessage("Exception in project " + jp.getElementName() + ": " + e.toString());
      }
    }
    if (nothing) {
      if (Log.on) {
        Log.log("No relevant objects");
      }
      showMessage("No relevant objects");
    }

  }

  /**
   * Iterates over all the package fragment roots in the map,
   * calling start/doit/end for each package fragment root and
   * its Collection.  The map must be indexed by package fragment root.
   * @param map The map containing IPackageFragmentRoot keys and Collection values
   */
  public void iterateByPFR(final Map<IPackageFragmentRoot, 
                                     Collection<IAdaptable>>  map) {
    boolean nothing = true;
    for (Map.Entry<IPackageFragmentRoot, Collection<IAdaptable>> entry: map.entrySet()) {
      final IPackageFragmentRoot pfr = entry.getKey();
      final Collection<IAdaptable> elements = entry.getValue();
      if (!elements.isEmpty()) {
        nothing = false;
      }
      // Catch exceptions here so that we can continue on
      // with other items to be done
      try {
        if (!start(pfr, elements)) { 
          continue;
        }
        for (IAdaptable ad: elements) {
          final boolean ok = doit(ad);
          if (!ok) {
            showMessage("Unable to process an item of type " + ad.getClass());
          }
        }
        end(pfr.getJavaProject(), elements);
//      } catch (JMLEclipseCancel e) {
//        throw e;
      }
      catch (Exception e) {
        showMessage("Exception while acting on folder " + 
                    pfr.getElementName() + ": " + e.getMessage());
        Log.errorlog("Exception while acting on folder " + pfr.getElementName(),e);
      }
    }
    if (nothing) {
      showMessage("No relevant objects");
    }

  }

  /**
   * Sorts the projects in the map into an order such that any project
   * follows all of those it requires (that are in the map).
   * 
   * @param map A map whose keys are IProject objects.
   * @return An array of the keys of the map (which are IProject
   *     objects) sorted so that any project comes after projects
   *     that it requires.
   */
  protected IProject[] orderedProjects(final Map<IJavaProject, Collection<IAdaptable>> map) {
    final Set<IJavaProject> s = map.keySet();
    final IProject [] projects = new IProject[s.size()];
    int j = 0;
    for (IJavaProject proj : s) {
      projects[j++] = proj.getProject(); 
    }
    return ResourcesPlugin.getWorkspace().computeProjectOrder(projects).projects;
  }  
  
  /**
   * Returns an iterator over the project 
   * array returned by orderedProjects().
   * 
   * @param map
   * @return An Iterator that iterates over the keys of the map 
   *     (which are IProject objects) in order, with projects
   *     required coming before those that require them.
   */
  protected Iterator<IProject> orderedProjectIterator(final Map<IJavaProject, Collection<IAdaptable>> map) {
    return Arrays.asList(orderedProjects(map)).iterator();
  }
  
  /**
   * Called prior to processing the Collection of elements for the
   * given project.  If false is returned, this will be the end of 
   * processing for this project; if true is returned, then doit is 
   * called on each element of the Collection followed by calling end.
   * @param jp  The IJavaProject whose elements are being processed
   * @param elements The filenames of files to be processed
   * @return Return true if processing is to continue with each 
   * element; false if this method contains all the processing to
   *  be performed
   * @throws Exception
   */
  protected boolean start(final IJavaProject jp, 
                          final Collection<IAdaptable> elements) 
    throws Exception { 
    return true; 
  }

  /**
   * Called prior to processing the Collection of elements for the
   * given package-fragment-root.  If false is returned, this will be the end of 
   * processing for this package-fragment-root; if true is returned, then doit is 
   * called on each element of the Collection followed by calling end.
   * @param pfr  The IPackageFragmentRoot whose elements are being processed
   * @param elements The filenames of files to be processed
   * @return Return true if processing is to continue with each element; 
   * false if this method contains all the processing to be performed
   * @throws Exception
   */
  protected boolean start(IPackageFragmentRoot pfr, Collection<IAdaptable> elements) throws Exception { return true; }
  

  /**
   * Called after each element of a given project has 
   * been processed (via doit).
   * @param jp  The project whose elements are being processed
   * @param elements  The filenames of the files/folders being processed
   * @return Ignored // FIXME
   * @throws Exception
   */
  protected boolean end(IJavaProject jp, Collection<IAdaptable> elements) throws Exception { return true; }
  
  /**
   * Executes the processing for one element (the argument).
   * @param o The object to be processed
   * @return true if the object was processed successfully, false otherwise.
   * @throws Exception
   */
  protected boolean doit(final IAdaptable o)
    throws Exception {
    return true;
  }
  
  /**
   * Calls doit for each java project within the workspace;
   * continues on even if one project fails.
   * 
   * @return false if any one project fails, true if all succeed
   * @throws Exception
   */
  protected boolean doWorkspace() throws Exception {
    boolean b = true;
    final IJavaProject[] projects = Utils.getJavaProjects();
    for (int i = 0; i < projects.length; ++i) {
      final boolean bb = doit(projects[i]);
      if (!bb) {
        b = false;
      }
    }
    return b;
  }
  /**
   * This calls doit on every (non-archive) package fragment within the project.
   * 
   * @param p - the project whose packages are to be operated on
   * @return false if any one item fails, true if all succeed
   * @throws Exception
   */
  protected boolean doProject(final IJavaProject p) throws Exception {
    final IPackageFragmentRoot[] pr = p.getPackageFragmentRoots();
    final boolean b = true;
    for (int kk = 0; kk < pr.length; ++kk) {
      if (pr[kk].isArchive()) {
        continue;
      }
      doPackageFragmentRoot(pr[kk]);
    }
    return b;
  }

  /**
   * This calls doit on every package within the package fragment root.
   * 
   * @param p - the package fragment whose compilation units are to be operated on
   * @return false if any one item fails, true if all succeed
   * @throws Exception
   */
  protected boolean doPackageFragmentRoot(final IPackageFragmentRoot p) throws Exception {
    final IJavaElement[] pfs = p.getChildren();
    boolean b = true;
    for (int i = 0; i < pfs.length; ++i) {
      final IPackageFragment pf = (IPackageFragment)pfs[i];
      final boolean bb = doPackageFragment(pf);
      if (!bb) {
        b = false;
      }
    }
    return b;
  }
  
  /**
   * This calls doit on every compilation unit within the package fragment.
   * 
   * @param p - the package fragment whose compilation units are to be operated on
   * @return false if any one item fails, true if all succeed
   * @throws Exception
   */
  protected boolean doPackageFragment(final IPackageFragment p) throws Exception {
    final ICompilationUnit[] cus = p.getCompilationUnits();
    boolean b = true;
    for (int j = 0; j < cus.length; ++j) {
      final ICompilationUnit cu = cus[j];
      final boolean bb = doit(cu);
      if (!bb) {
        b = false;
      }
    }
    return b;
  }

}
// FIXME -need javadoc comments
  

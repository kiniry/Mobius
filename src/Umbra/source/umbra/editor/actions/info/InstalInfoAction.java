/*
 * Created on 2005-09-06
 */
package umbra.editor.actions.info;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Enumeration;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.browser.IWebBrowser;
import org.eclipse.ui.browser.IWorkbenchBrowserSupport;
import org.eclipse.ui.help.IWorkbenchHelpSystem;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraPlugin;

/**
 * TODO
 *
 * @author Wojtek Wąs
 */
public class InstalInfoAction implements IEditorActionDelegate {

  /**
   * TODO
   */
  private IEditorPart editor;

  /**
   * TODO
   */
  public final void setActiveEditor(final IAction action, final IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * TODO
   */
  public final void run(final IAction an_action) {

    IWorkbenchHelpSystem help = PlatformUI.getWorkbench().getHelpSystem();
    //FIXME open something more specific, note that it is tricky to know the
    // proper ID to open
    // it should open Info/info.txt
    help.displayHelp();
  }

  /**
   * TODO
   */
  public void selectionChanged(final IAction action, 
                               final ISelection selection) {
  }
}

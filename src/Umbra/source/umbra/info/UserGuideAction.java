/*
 * Created on 2005-09-06
 */
package umbra.info;

import java.net.URL;

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

import umbra.UmbraPlugin;

/**
 * The class implements the behaviour in case the User Guide button
 * is pressed.
 * 
 * @author Wojtek W±s
 */
public class UserGuideAction implements IEditorActionDelegate {

	/**
	 * The method sets the editor associated with the action.
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
	}

	/**
	 * The method shows the content of the file with the guiding 
	 * instructions.
	 */
	public void run(IAction action) {

		UmbraPlugin plugin = UmbraPlugin.getDefault();
		IWorkbenchBrowserSupport bs = PlatformUI.getWorkbench().
		                                         getBrowserSupport();
		IWebBrowser wb;
		try {
			wb = bs.createBrowser("Umbra Guide");
		} catch (PartInitException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return;
		}
		
		URL url = FileLocator.find(plugin.getBundle(), 
				                   new Path("Info/guide.txt"), 
				                   null);
		try {
			wb.openURL(url);
		} catch (PartInitException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}


	/**
	 * Currently, does nothing.
	 */
	public void selectionChanged(IAction action, ISelection selection) {

	}

}

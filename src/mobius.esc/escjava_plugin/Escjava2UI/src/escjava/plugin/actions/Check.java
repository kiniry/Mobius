package escjava.plugin.actions;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.swt.widgets.Shell;

import pluginlib.Log;
import pluginlib.Utils;
import escjava.plugin.EscjavaChecker;
import escjava.plugin.EscjavaMarker;

/**
 * This class implements the action for checking
 * files using EscJava2
 * 
 * @author David R. Cok
 */
public class Check extends EscjavaAction {
	public final void run(final IAction action) {
	  Shell shell = window.getShell();
		try {
		  List<IAdaptable> list = Utils.getSelectedElements(selection,window);
			if (list.size() == 0) {
				Utils.showMessageInUI(shell, "ESCJava Plugin", "Nothing to check");
			}
			for (IAdaptable adap: list) {
			  if (!(adap instanceof IJavaElement)) 
			    continue;
				IJavaElement e = (IJavaElement) adap;
				boolean checked = checkJavaElement(e);
				if (!checked) {
					String msg = "Cannot check " + e.getClass();
					Utils.showMessageInUI(shell, "ESCJava Plugin", msg);
				}
			}
			
		} 
		catch (Exception e) {
			if (window != null) {
				Utils.showMessageInUI(
						shell,
						"ESCJava Plugin - exception",
						e.toString());
			}			
		}
	}
	/**TODO
	 * @param element
	 * @return
	 * @throws Exception
	 */
	public static boolean checkJavaElement(IJavaElement element) 
	throws Exception {
		if (element instanceof IJavaProject) {
			checkProject( (IJavaProject)element );
		}
		else if (element instanceof IPackageFragment) {
			checkPackage( (IPackageFragment)element );
		}
		else if (element instanceof ICompilationUnit) {
			checkCompilationUnit( (ICompilationUnit)element );
		}
		else if (element instanceof IType) {
			checkType((IType)element);
		}
		else {
			return false;
		}
		return true;
	}
	
	/**TODO
	 * @param javaProject
	 * @throws Exception
	 */
	private static void checkProject(IJavaProject javaProject) 
	throws Exception {
		List<String> filesToCheck = new LinkedList<String>();
		for (IPackageFragment p: javaProject.getPackageFragments()) {
			for (ICompilationUnit cu: p.getCompilationUnits()) {
				filesToCheck.add(cu.getResource().getLocation().toOSString());				
			}
			// FIXME - put package names on command-line?
		}
		EscjavaMarker.clearMarkers(javaProject.getProject());
		try {
		    // FIXME - multi-thread this?
			EscjavaChecker ec = new EscjavaChecker(javaProject);
			ec.run(filesToCheck);
		} 
		catch (Exception e) {
			Log.errorlog("Exception occurred in running ESCJava checks: ",e);
		}
	}
	
	/** TODO
	 * @param p
	 * @throws Exception
	 */
	private static void checkPackage(IPackageFragment p) 
	throws Exception {
		List<String> filesToCheck = new LinkedList<String>();
		for (ICompilationUnit cu: p.getCompilationUnits()) {
			filesToCheck.add(cu.getResource().getLocation().toOSString());				
		}
		EscjavaMarker.clearMarkers(p.getResource());
		// FIXME - put package names on command-line?
		try {
		    // FIXME - multi-thread this?
			EscjavaChecker ec = new EscjavaChecker(p.getJavaProject());
			ec.run(filesToCheck);
		} catch (Exception e) {
			Log.errorlog("Exception occurred in running ESCJava checks: ",e);
		}		
	}
	
	/**TODO
	 * @param p
	 * @throws JavaModelException
	 * @throws CoreException
	 */
	private static void checkCompilationUnit(ICompilationUnit p) 
				throws JavaModelException, CoreException  {
		IResource resource = p.getUnderlyingResource();
		ArrayList<String> list = new ArrayList<String>(1);
		list.add(resource.getLocation().toOSString());
		IJavaProject jp = p.getJavaProject();
		EscjavaMarker.clearMarkers(resource);
		try {
		    // FIXME - multi-thread this?
			EscjavaChecker ec = new EscjavaChecker(jp);
			ec.run(list);
		} 
		catch (Exception e) {
			Log.errorlog("Exception occurred in running ESCJava checks: ",e);
		}
	}
	
	/**TODO
	 * @param p
	 */
	private static void checkType(IType p) {
		System.out.println("TYPE " + p.getFullyQualifiedName());
		// FIXME
	}
	
	// FIXME - want to check only a method as well.

}
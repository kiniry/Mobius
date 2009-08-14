package canapa.actions;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import canapa.util.RunCanapa;

public class RunCanapaAction implements IWorkbenchWindowActionDelegate {
	IWorkbenchWindow window;
	ITreeSelection selection;

	public void dispose() {
	}

	public void init(IWorkbenchWindow window) {
		this.window = window;

	}

	public void run(IAction action) {
		if (selection == null) {
			return;
		}
		List icus = getSelectedIcu(selection);
		for (int i = 0; i < icus.size(); i++) {
			ICompilationUnit icu = (ICompilationUnit) icus.get(i);
			if (icu.getResource() != null
					&& icu.getResource().getLocation() != null) {
				try {
					String classPath = getProjectClassPath(icu.getJavaProject());
					RunCanapa.runCanapaFile(icu.getResource().getLocation()
							.toOSString(), classPath);
				} catch (JavaModelException e) {
					e.printStackTrace();
				}
			}
		}

	}

	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof ITreeSelection) {
			this.selection = (ITreeSelection) selection;
		}

	}

	public List getSelectedIcu(ITreeSelection selection) {
		List result = new LinkedList();
		Iterator iter = selection.iterator();
		while (iter.hasNext()) {
			Object obj = iter.next();
			if (obj instanceof ICompilationUnit) {
				result.add(obj);
			} else {
				continue;

			}
		}
		return result;
	}

	private String getOutputLocation(final IJavaProject project)
			throws JavaModelException {
		IWorkspaceRoot wr = ResourcesPlugin.getWorkspace().getRoot();
		IPath oloc = project.getOutputLocation();
		IPath proot = project.getPath();
		if (!oloc.equals(proot))
			return wr.getFolder(oloc).getLocation().toOSString();
		else
			return project.getResource().getLocation().toOSString();
	}

	private String getProjectClassPath(final IJavaProject project)
			throws JavaModelException {
		IWorkspaceRoot wr = ResourcesPlugin.getWorkspace().getRoot();
		StringBuffer result = new StringBuffer();
		result.append(getOutputLocation(project));
		for (int i = 0; i < project.getRawClasspath().length; i++) {
			IClasspathEntry entry = project.getRawClasspath()[i];
			switch (entry.getEntryKind()) {
			case IClasspathEntry.CPE_SOURCE:
				if (entry.getPath() != null) {
					result.append(java.io.File.pathSeparator
							+ ResourcesPlugin.getWorkspace().getRoot()
									.getFolder(entry.getPath()).getLocation()
									.toOSString());
				}
				if (entry.getOutputLocation() != null)
					result.append(java.io.File.pathSeparator
							+ entry.getOutputLocation());
				break;
			case IClasspathEntry.CPE_LIBRARY:
				result.append(java.io.File.pathSeparator
						+ wr.getFolder(entry.getPath()).getLocation()
								.toOSString());
			default:
				break;
			}
		}

		return result.toString();
	}
}

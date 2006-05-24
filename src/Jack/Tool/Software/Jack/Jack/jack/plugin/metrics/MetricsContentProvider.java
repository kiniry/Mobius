//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProofContentProvider.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.metrics;

import jack.plugin.JackPlugin;
import jack.plugin.JpovUtil;
import jack.plugin.edit.EditedFile;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import jpov.JpoFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

/**
 * Content provider providing content for ProofTaskList elements.
 * 
 * @author A. Requet, L. Burdy
 */
public class MetricsContentProvider implements IStructuredContentProvider {
	/**
	 * The current viewer.
	 */
	private Viewer viewer;
	private Display dsp;

	private MetricsFilterWindow mfw;

	/*@ invariant (viewer == null) == (dsp == null); */

	MetricsContentProvider(MetricsFilterWindow filterw) {
		mfw = filterw;
	}

	public Object[] getElements(Object input_element) {
		Object[] res;
		if (input_element instanceof IJavaProject) {
			try {
				IJavaElement[] jea =
					((IJavaProject) input_element).getChildren();
				ArrayList al = new ArrayList();
				for (int i = 0; i < jea.length; i++) {
					List l = Arrays.asList(getElements(jea[i]));
					al.addAll(l);
				}
				return al.toArray();
			} catch (JavaModelException jme) {
				;
			}
		} else if (input_element instanceof IPackageFragmentRoot) {
			try {
				IJavaElement[] jea =
					((IPackageFragmentRoot) input_element).getChildren();
				ArrayList al = new ArrayList();
				for (int i = 0; i < jea.length; i++) {
					List l = Arrays.asList(getElements(jea[i]));
					al.addAll(l);
				}
				return al.toArray();
			} catch (JavaModelException jme) {
				;
			}
		} else if (input_element instanceof IPackageFragment)
			try {
				return ((IPackageFragment) input_element).getChildren();
			} catch (JavaModelException jme) {
				;
			} else if (input_element instanceof ICompilationUnit) {
			if (mfw.getFilterType() == MetricsFilterWindow.RESSOURCE_ONLY) {
				JpoFile jpov = getJpo((ICompilationUnit) input_element);
				return jpov.getJmlFile().getGoals().toArray();
			} else {
				res = new Object[1];
				res[0] = input_element;
			}
			return res;
		}

		return new Object[0];
	}

	private static JpoFile getJpo(ICompilationUnit c) {
		IFile jpo_file = JackPlugin.getJpoFile(c);
		if (jpo_file != null) {
			try {
				return JpovUtil.loadJpoFile(new EditedFile(jpo_file));
			} catch (Exception e) {
				;
			}
		}
		return null;
	}
	public void dispose() {
	}

	public void inputChanged(
		Viewer viewer,
		Object old_input,
		Object new_input) {
		// updates the viewer
		this.viewer = viewer;
		if (viewer != null) {
			dsp = viewer.getControl().getDisplay();
		} else {
			dsp = null;
		}
	}

	/**
	 * Called by the ProofList when its content changes.
	 * This methods asks the viewer to refresh itself.
	 */
	public void contentChanged() {
		if (viewer != null) {
			// refresh the view		
			dsp.syncExec(new Runnable() {
				public void run() {
					viewer.refresh();
				}
			});
		}
	}
}

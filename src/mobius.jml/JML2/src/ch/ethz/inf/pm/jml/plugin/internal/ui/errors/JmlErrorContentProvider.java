/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2003-2008 Swiss Federal Institute of Technology Zurich
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Paolo Bazzi, Summer 2006
 *
 */


package ch.ethz.inf.pm.jml.plugin.internal.ui.errors;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Control;

import ch.ethz.inf.pm.jml.plugin.IJmlListener;
import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlErrorContentProvider implements IStructuredContentProvider, IJmlListener {

	private TableViewer viewer;
//	private List<JmlErrorElement> lastResults = new ArrayList<JmlErrorElement>();

	public JmlErrorContentProvider()
	{
		JmlPlugin.getDefault().addListener(this);
	}

	public void dispose() {
		JmlPlugin.getDefault().removeListener(this);
	}

	@SuppressWarnings("unchecked")
	public Object[] getElements(Object inputElement)
	{
		if (inputElement instanceof List) // <JmlErrorElement>
		{
			return ((List<JmlErrorElement>)inputElement).toArray();
		} else {
			return null;
		}
	}

	public void inputChanged(Viewer tableViewer, Object oldInput, Object newInput) {
		viewer= (TableViewer)tableViewer;
	}

	@SuppressWarnings("unchecked")
	private List<JmlErrorElement> getResults() {
		return (List<JmlErrorElement>)viewer.getInput();
	}

	// private void setResults(List<JmlErrorElement> res) {
	// 	viewer.setInput(res);
	// }

	public void jmlStartedMultiple() {
		updateView(viewer, new ArrayList<JmlErrorElement>());
	}

	public void jmlStarted(IFile file) {
		/* List<JmlErrorElement> results = new ArrayList<JmlErrorElement>(getResults());
		lastResults.clear();

		Iterator<JmlErrorElement> iter = results.iterator();
		while (iter.hasNext()) {
			JmlErrorElement elem = iter.next();
			if (!elem.getFile().getName().equals(file.getName())) {
				lastResults.add(elem);
			}	else {
				//System.out.println("removed elem = " + elem);
			}
		}
		updateView(viewer, lastResults); */
	}

	public void jmlFinished(IFile file, final List<JmlErrorElement> result) {
		List<JmlErrorElement> res = getResults();
		res.addAll(0, result);

		updateView(viewer, res);
	}

	public void jmlFinishedMultiple() {
	}

	private static void updateView(final TableViewer vw, final List<JmlErrorElement> res) {
		Control ctrl = vw.getControl();
		if (ctrl == null || ctrl.isDisposed())
			return;
		vw.getControl().getDisplay().syncExec(new Runnable() {
			public void run() {
				if (!vw.getControl().isDisposed()) {
					vw.setInput(res);
					vw.refresh();
				}
			}
		});
	}
}

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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.ViewPart;

import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;

/**
 * @author Paolo Bazzi
 * @author WMD
 */
public class JmlErrorView extends ViewPart {
	public static final String ID = "ch.ethz.inf.pm.jml.plugin.ui.JmlErrorView";

	private TableViewer viewer;

	@Override
	public void createPartControl(Composite parent) {
		Table table = new Table(parent, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER | 	SWT.FULL_SELECTION);
		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		TableColumn c = new TableColumn(table, SWT.NONE,0);
		c.setText("Line");
		c.setWidth(35);
		c.setAlignment(SWT.RIGHT);

		c = new TableColumn(table, SWT.NONE, 1);
		c.setText("Char");
		c.setWidth(35);
		c.setAlignment(SWT.RIGHT);

		c = new TableColumn(table, SWT.NONE, 2);
		c.setText("Error");
		c.setWidth(500);

		c = new TableColumn(table, SWT.NONE, 3);
		c.setText("Resource");
		c.setWidth(250);

		c = new TableColumn(table, SWT.NONE, 4);
		c.setText("JML Reference");
		c.setWidth(250);

		/*
		table.addSelectionListener(new SelectionAdapter() {
			public void widgetDefaultSelected(SelectionEvent e) {
				handleDefaultSelected();
			}
		});
		 */

		viewer = new TableViewer(table);
		viewer.setContentProvider(new JmlErrorContentProvider());
		viewer.setLabelProvider(new JmlErrorLabelProvider());
		viewer.setInput(new ArrayList<JmlErrorElement>());

		getSite().setSelectionProvider(viewer);

		viewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(SelectionChangedEvent event) {
				ISelection sel = event.getSelection();

				if (sel instanceof StructuredSelection) {
					StructuredSelection ssel = (StructuredSelection) sel;
					Object elem = ssel.getFirstElement();

					if (elem instanceof JmlErrorElement) {
						JmlErrorElement jee = (JmlErrorElement) elem;
						IFile f = jee.getFile();

						Map<String, Object> mat = new HashMap<String, Object>();
 					   	mat.put(IMarker.LINE_NUMBER, jee.getLineNr());
 					   	// the char seem to be relative to the beginning of file,
 					   	// not within the line. So don't use them...
						// mat.put(IMarker.CHAR_START, jee.getCharNr());
						// mat.put(IMarker.CHAR_END, jee.getCharNr()+1);

 					   	try {
							IMarker marker = f.createMarker(IMarker.TEXT);
							marker.setAttributes(mat);

							IWorkbenchPage page = JmlPlugin.getDefault()
									.getWorkbench().getActiveWorkbenchWindow()
									.getActivePage();
							IDE.openEditor(page, marker);

							/*
							 * The following code would highlight the character at the error
							 * position. I like it better if the whole line is highlighted,
							 * or if this would be edited to highlight till the end of the line.
							if (jee.getCharNr() > 0) {
								// as I said above, there has to be a better way
								// to do this... but this should work
								ISelectionService selser = getSite()
										.getWorkbenchWindow()
										.getSelectionService();
								ISelection mtextsel = selser.getSelection();

								if (mtextsel instanceof ITextSelection) {
									ITextSelection textsel = (ITextSelection) mtextsel;
									int lineoff = textsel.getOffset();

									mat.put(IMarker.CHAR_START, lineoff + jee.getCharNr()+1);
									mat.put(IMarker.CHAR_END, lineoff + jee.getCharNr()+2);
									marker.setAttributes(mat);
									IDE.openEditor(page, marker);
								}
							}
							*/

							marker.delete();

							JmlErrorView.this.setFocus();
						} catch (Exception e) {
							JmlPlugin.getDefault().getLog().log(
									new Status(IStatus.ERROR,
											JmlPlugin.PLUGIN_ID,
											"Problem when trying to switch view!", e));
 					   	}
					}
				}
			}});

/*
		WorkbenchHelp.setHelp(viewer.getControl(), "org.eclipse.contribution.junit.autoTestContext"); //$NON-NLS-1$
*/
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	public void setInput(List<JmlErrorElement> results)	{
		viewer.setInput(results);
	}
}

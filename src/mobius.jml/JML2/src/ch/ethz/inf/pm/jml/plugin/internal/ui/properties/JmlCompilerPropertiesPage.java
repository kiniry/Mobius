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

package ch.ethz.inf.pm.jml.plugin.internal.ui.properties;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlCompilerProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlCompilerPropertiesPage extends JmlPropertiesPage {

	private Button print;
	private Button nowrite;
	private Button noreflection;
	private Button noredundancy;
	private Button recursiveType;
	private Text packageName;
	private Button noSource;
	private Button neutralContext;
	private Text filter;
	private Button oldSemantics;
	private Button mustBeExecutable;


	@Override
	protected Control createPreferenceContent(Composite comp) {
		final ScrolledPropPageContent sc1 = new ScrolledPropPageContent(comp);
		Composite scbody= sc1.getBody();
		GridLayout layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		scbody.setLayout(layout);

		Composite fControlsComposite= new Composite(scbody, SWT.NONE);
		fControlsComposite.setFont(scbody.getFont());
		fControlsComposite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));
		layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		layout.numColumns= 1;
		fControlsComposite.setLayout(layout);

		try {
			JmlPropertiesProvider compilerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.COMPILER_DEF_PROPERTIES_FILE);
			Composite composite = createDefaultComposite(fControlsComposite);
			IProject project = getProject();

			GridLayout gridLayout = new GridLayout();
		    gridLayout.numColumns = 1;
			composite.setLayout(gridLayout);

			GridData gdtextfield = new GridData();
			gdtextfield.widthHint = convertWidthInCharsToPixels(TEXT_FIELD_WIDE_WIDTH);
			// gdtextfield.horizontalAlignment = GridData.FILL;
			// gdtextfield.grabExcessHorizontalSpace = true;

			print = new Button(composite,SWT.CHECK);
			print.setText("Print instrumented source code instead of bytecode (--print)");
			print.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.PRINT,project));

			nowrite = new Button(composite,SWT.CHECK);
			nowrite.setText("Only typecheck files, doesn't generate code (--nowrite)");
			nowrite.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_WRITE,project));

			noreflection = new Button(composite,SWT.CHECK);
			noreflection.setText("Don't use reflection for specification inheritance (--noreflection)");
			noreflection.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_REFLECTION,project));

			noredundancy = new Button(composite,SWT.CHECK);
			noredundancy.setText("Don't check redundant specifications (--noredundancy)");
			noredundancy.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_REDUNDANCY,project));

			recursiveType = new Button(composite,SWT.CHECK);
			recursiveType.setText("Enable typechecking of recursively referenced types (--recursiveType)");
			recursiveType.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.RECURSIVE_TYPE,project));

			Label packageNameLabel = new Label(composite,SWT.NONE);
			packageNameLabel.setText("Package name or prefix (--packageName <pkg-name>):");
			packageName = new Text(composite, SWT.BORDER);
			packageName.setLayoutData(gdtextfield);
			packageName.setText(compilerProps.getProperty(JmlCompilerProperties.PACKAGE_NAME, project));

			noSource = new Button(composite,SWT.CHECK);
			noSource.setText("Compile even if no source file is available (--noSource)");
			noSource.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_SOURCE,project));

			neutralContext = new Button(composite,SWT.CHECK);
			neutralContext.setText("Use neutral context instead of contextual interpretation (--neutralContext)");
			neutralContext.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.NEUTRAL_CONTEXT,project));

			Label filterLabel = new Label(composite,SWT.NONE);
			filterLabel.setText("Warning filter (--filter <qualified-name>):");
			filter = new Text(composite, SWT.BORDER);
			filter.setLayoutData(gdtextfield);
			filter.setText(compilerProps.getProperty(JmlCompilerProperties.FILTER, project));

			oldSemantics = new Button(composite,SWT.CHECK);
			oldSemantics.setText("Use old expression translation mechanism that emulates 2-valued logic (--oldSemantics)");
			oldSemantics.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.OLD_SEMANTICS,project));

			mustBeExecutable = new Button(composite,SWT.CHECK);
			mustBeExecutable.setText("Consider non-executable clauses as false assertions (--mustBeExecutable)");
			mustBeExecutable.setSelection(compilerProps.getBooleanProperty(JmlCompilerProperties.MUST_BE_EXECUTABLE,project));

		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
		return sc1;
	}

	@Override
	protected void performDefaults() {
		JmlPropertiesProvider compilerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.COMPILER_DEF_PROPERTIES_FILE);
		try {
			packageName.setText(compilerProps.getDefaultProperty(JmlCompilerProperties.PACKAGE_NAME));
			filter.setText(compilerProps.getDefaultProperty(JmlCompilerProperties.FILTER));
			oldSemantics.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.OLD_SEMANTICS));
			mustBeExecutable.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.MUST_BE_EXECUTABLE));
			neutralContext.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.NEUTRAL_CONTEXT));
			noSource.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.NO_SOURCE));
			noredundancy.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.NO_REDUNDANCY));
			noreflection.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.NO_REFLECTION));
			nowrite.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.NO_WRITE));
			print.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.PRINT));
			recursiveType.setSelection(compilerProps.getBooleanDefaultProperty(JmlCompilerProperties.RECURSIVE_TYPE));
 		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
	}

	@Override
	public boolean performOk() {
		IProject p = getProject();
		try {
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.MUST_BE_EXECUTABLE), String.valueOf(mustBeExecutable.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.OLD_SEMANTICS), String.valueOf(oldSemantics.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.NO_REFLECTION), String.valueOf(noreflection.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.NO_WRITE), String.valueOf(nowrite.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.PACKAGE_NAME), packageName.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.FILTER), filter.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.PRINT), String.valueOf(print.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.RECURSIVE_TYPE), String.valueOf(recursiveType.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.NEUTRAL_CONTEXT), String.valueOf(neutralContext.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.NO_SOURCE), String.valueOf(noSource.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCompilerProperties.NO_REDUNDANCY), String.valueOf(noredundancy.getSelection()));
		} catch (CoreException e) {
	          JmlPlugin.getDefault().getLog().log(
	                    new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.getMessage(), e));
			return false;
		}
		return true;
	}
}

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
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlCheckerProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;

/**
 * The properties page for the checker component.
 *
 * @author Paolo Bazzi
 * @author WMD
 *
 */
public class JmlCheckerPropertiesPage extends JmlPropertiesPage {

	private Button Assignable;
	private Button Quiet;
	private Button UnsafeOpWarnings;
	private Combo admissibility;
	private Button assignable;
	private Text classpath;
	private Button debug;
	private Button defaultNonNull;
	private Button deprecation;
	private Text destination;
	private Text excludeFiles;
	private Text experiment;
	private Text filter;
	private Text xlint;
	private Button generic;
	private Button keepGoing;
	private Button multijava;
	private Button nonnull;
	private Button nonnulltypes;
	private Button xArrayNNTS;
	private Button purity;
	private Button quiet;
	private Button recursive;
	private Button relaxed;
	private Button safemath;
	private Text source;
	private Text sourcePath;
	private Text universesx;
	private Button verbose;
	private Text warning;


	@Override
	protected Control createPreferenceContent(Composite comp) {
		final ScrolledPropPageContent sc1 = new ScrolledPropPageContent(comp);
		Composite composite = sc1.getBody();

		GridLayout layout= new GridLayout();
		// layout.marginHeight= 0;
		// layout.marginWidth= 0;
		// layout.numColumns= 1;
		composite.setLayout(layout);
		composite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));

		/*
		Composite fControlsComposite= new Composite(composite, SWT.NONE);
		fControlsComposite.setFont(composite.getFont());
		layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		layout.numColumns= 1;
		fControlsComposite.setLayout(layout);
		fControlsComposite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));
	*/

		try {
			addFirstSection(composite);
			addSeparator(composite);
			addSecondSection(composite);
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(),"Error",e.getMessage(),e.getStatus());
		}

		return sc1;
	}

	private void addFirstSection(Composite parent) throws CoreException {
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);
		Composite composite = createDefaultComposite(parent);
		IProject project = getProject();

		GridLayout gridLayout = new GridLayout();
	    gridLayout.numColumns = 1;
		composite.setLayout(gridLayout);
		composite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));

		GridData gdbigfield = new GridData();
		// gdbigfield.horizontalAlignment = GridData.FILL;
		// gdbigfield.grabExcessHorizontalSpace = true;
		gdbigfield.widthHint = convertWidthInCharsToPixels(TEXT_FIELD_WIDE_WIDTH);
		gdbigfield.heightHint = convertHeightInCharsToPixels(2);
		int bigfieldProps = SWT.MULTI | SWT.V_SCROLL | SWT.WRAP | SWT.BORDER;

		GridData gdSmall = new GridData();
		gdSmall.widthHint = convertWidthInCharsToPixels(TEXT_FIELD_SMALL_WIDTH);

		GridData gdWide= new GridData();
		gdWide.widthHint = convertWidthInCharsToPixels(TEXT_FIELD_WIDE_WIDTH);

		GridData gdCombo = new GridData();
		gdCombo.widthHint = convertWidthInCharsToPixels(COMBO_WIDTH);

		Composite c1 = new Composite(composite,SWT.NONE);
		GridLayout gridLayout2 = new GridLayout();
	    gridLayout2.numColumns = 2;
		gridLayout2.marginHeight= 0;
		gridLayout2.marginWidth= 0;
		c1.setLayout(gridLayout2);
		Label admissibilityLabel = new Label(c1, SWT.NONE);
		admissibilityLabel.setText("Check admissibility of invariants and represents clauses (--admissibility): ");
		admissibility = new Combo(c1,SWT.DROP_DOWN | SWT.READ_ONLY);
		admissibility.add(JmlCheckerProperties.ADMISSIBILITY_NONE,0);
		admissibility.add(JmlCheckerProperties.ADMISSIBILITY_CLASSICAL,1);
		admissibility.add(JmlCheckerProperties.ADMISSIBILITY_OWNERSHIP,2);
		admissibility.setLayoutData(gdCombo);
		String admissValue = checkerProps.getProperty(JmlCheckerProperties.ADMISSIBILITY,project);
		if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_NONE))
		{admissibility.select(0); }
		else if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_CLASSICAL))
		{admissibility.select(1); }
		else if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_OWNERSHIP))
		{ admissibility.select(2); }
		else // hard coded default
		{ admissibility.select(0); }

		Label universexLabel = new Label(composite, SWT.NONE);
		universexLabel.setText("Universe type system (--universesx <String>):\n(no, parse, check, dynchecks, purity, xbytecode, annotations, full)");
		universexLabel.setToolTipText("Comma-separated list of options.");
		universesx = new Text(composite, SWT.SINGLE | SWT.BORDER);
		universesx.setLayoutData(gdWide);
		universesx.setText(checkerProps.getProperty(JmlCheckerProperties.UNIVERSESX,project));
		/*
		universesx = new Combo(c1,SWT.DROP_DOWN | SWT.READ_ONLY);
		universesx.add(JmlCheckerProperties.UNIVERSESX_NO,0);
		universesx.add(JmlCheckerProperties.UNIVERSESX_PARSE,1);
		universesx.add(JmlCheckerProperties.UNIVERSESX_CHECK,2);
		universesx.add(JmlCheckerProperties.UNIVERSESX_FULL,3);
		universesx.setLayoutData(gdCombo);
		String universexValue = checkerProps.getProperty(JmlCheckerProperties.UNIVERSESX,project);
		if (universexValue .equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_NO)) {universesx.select(0); }
		else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_PARSE)) {universesx.select(1); }
		else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_CHECK)) {universesx.select(2); }
		else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_FULL)) {universesx.select(3); }
		else { universesx.select(0); } // hard coded default value
		 */

		Label classpathLabel = new Label(composite,SWT.NONE);
		classpathLabel.setText("Change classpath to the given system path (--classpath <classpath>):");
		classpathLabel.setToolTipText("The Java project and JML classpaths are added automatically. Usually empty.");
		classpath = new Text(composite, bigfieldProps);
		classpath.setLayoutData(gdbigfield);
		classpath.setText(checkerProps.getProperty(JmlCheckerProperties.CLASSPATH, project));

		Label destLabel = new Label(composite,SWT.NONE);
		destLabel.setText("Directory location to put output files (--destination <directory>):\n(path relative to project root, leading path separator is inserted automatically)");
		destLabel.setToolTipText("Defaults to \""+ ResourceConstants.DEFAULT_OUT + "\".");
		destination = new Text(composite, SWT.BORDER);
		destination.setLayoutData(gdWide);
		destination.setText(checkerProps.getProperty(JmlCheckerProperties.DESTINATION, project));

		Label excludeFileLabel = new Label(composite,SWT.NONE);
		excludeFileLabel.setText("Pattern (regex) of file names to exclude from processing (--excludefiles <pattern>):");
		excludeFiles = new Text(composite, bigfieldProps);
		excludeFiles.setLayoutData(gdbigfield);
		excludeFiles.setText(checkerProps.getProperty(JmlCheckerProperties.EXCLUDE_FILES, project));

		Label experimentLabel = new Label(composite,SWT.NONE);
		experimentLabel.setText("Specify experimental features such as symbol files (sym, symr, symw) (--experiment <exp-feature>):");
		experiment = new Text(composite, SWT.BORDER);
		experiment.setLayoutData(gdWide);
		experiment.setText(checkerProps.getProperty(JmlCheckerProperties.EXPERIMENT, project));

		Label filterLabel = new Label(composite,SWT.NONE);
		filterLabel.setText("Warning filter (--filter <qualified-name>):");
		filter = new Text(composite, SWT.BORDER);
		filter.setLayoutData(gdWide);
		filter.setText(checkerProps.getProperty(JmlCheckerProperties.FILTER, project));

		Label xlintLabel = new Label(composite,SWT.NONE);
		xlintLabel.setText("The recommended warnings to enable (--Xlint <identifier-list>):");
		xlint = new Text(composite, SWT.BORDER);
		xlint.setLayoutData(gdWide);
		xlint.setText(checkerProps.getProperty(JmlCheckerProperties.XLINT, project));


		Label sourcePathLabel = new Label(composite,SWT.NONE);
		sourcePathLabel.setText("Directory path to search for packages listed on the command-line (--sourcepath <directory-list>):");
		sourcePathLabel.setToolTipText("Defaults to the classpath. Usually empty.");
		sourcePath = new Text(composite, bigfieldProps);
		sourcePath.setLayoutData(gdbigfield);
		sourcePath.setText(checkerProps.getProperty(JmlCheckerProperties.SOURCE_PATH, project));

		Label sourceLabel = new Label(composite,SWT.NONE);
		sourceLabel.setText("When set to 1.4 the compiler accepts code containing Java 1.4 assert statements (--source <release-number>):");
		source = new Text(composite, SWT.BORDER);
		source.setLayoutData(gdSmall);
		source.setText(checkerProps.getProperty(JmlCheckerProperties.SOURCE, project));

		Label warningLabel = new Label(composite,SWT.NONE);
		warningLabel.setText("'Pickiness' of warnings to be displayed (--warning <int>):");
		warning = new Text(composite, SWT.BORDER);
		warning.setLayoutData(gdSmall);
		warning.setText(checkerProps.getProperty(JmlCheckerProperties.WARNING, project));
	}

	private void addSecondSection(Composite parent) throws CoreException {
		Composite composite = createDefaultComposite(parent);
		IProject project = getProject();
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);

		GridLayout gridLayout = new GridLayout();
	    gridLayout.numColumns = 1;
		composite.setLayout(gridLayout);
		composite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));

		recursive = new Button(composite,SWT.CHECK);
		recursive.setText("Process all subdirectories recursively from the given directory (--recursive)");
		recursive.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.RECURSIVE,project));

		Quiet = new Button(composite,SWT.CHECK);
		Quiet.setText("Shut off all typechecking informational messages (--Quiet)");
		Quiet.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.QUIET,project));

		quiet = new Button(composite,SWT.CHECK);
		quiet.setText("Suppress information on compilation passes completed (--quiet)");
		quiet.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.qUIET,project));

		debug = new Button(composite,SWT.CHECK);
		debug.setText("Produce (copious) debugging information (--debug)");
		debug.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.DEBUG,project));

		verbose = new Button(composite,SWT.CHECK);
		verbose.setText("Display verbose information during compilation (--verbose)");
		verbose.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.VERBOSE,project));

		Assignable = new Button(composite,SWT.CHECK);
		Assignable.setText("Check that a method with an assignable clause does not call methods that do not have an assignable clause (--Assignable)");
		Assignable.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.ASSIGNABLE,project));

		assignable = new Button(composite,SWT.CHECK);
		assignable.setText("Check that each non-pure heavyweight method specification case has an assignable clause (--assignable)");
		assignable.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.aSSIGNABLE,project));

		purity = new Button(composite,SWT.CHECK);
		purity.setText("Check for purity in JML specification expressions (--purity)");
		purity.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.PURITY,project));

		deprecation = new Button(composite,SWT.CHECK);
		deprecation.setText("Test for deprecated members (--deprecation)");
		deprecation.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.DEPRECATION,project));

		generic = new Button(composite,SWT.CHECK);
		generic.setText("Accept Generic source code (--generic)");
		generic.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.GENERIC,project));

		keepGoing = new Button(composite,SWT.CHECK);
		keepGoing.setText("Keep going when errors are encountered (may cause exceptions) (--keepGoing)");
		keepGoing.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.KEEP_GOING,project));

		multijava = new Button(composite,SWT.CHECK);
		multijava.setText("Accept MultiJava source code (--multijava)");
		multijava.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.MULTIJAVA,project));

		relaxed = new Button(composite,SWT.CHECK);
		relaxed.setText("Accept Relaxed MultiJava source code (--relaxed)");
		relaxed.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.RELAXED,project));

		defaultNonNull = new Button(composite,SWT.CHECK);
		defaultNonNull.setText("Make reference paramenters, fields and method return types non_null by default (--defaultNonNull)");
		defaultNonNull.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.DEFAULT_NON_NULL,project));

		nonnull = new Button(composite,SWT.CHECK);
		nonnull.setText("Statistics of non_null application (--nonnull)");
		nonnull.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.NON_NULL,project));

		nonnulltypes = new Button(composite,SWT.CHECK);
		nonnulltypes.setText("Use the non_null type system (--nonnulltypes)");
		nonnulltypes.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.NON_NULL_TYPES,project));

		xArrayNNTS = new Button(composite,SWT.CHECK);
		xArrayNNTS.setText("Use the experimental array handling in the NonNull Type System (--xArrayNNTS)");
		xArrayNNTS.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.XARRAY_NNTS,project));

		UnsafeOpWarnings = new Button(composite,SWT.CHECK);
		UnsafeOpWarnings.setText("Produce warnings if an unsafe arithmetic operators is used in an assertion for which the math mode has not been explicitly set (--UnsafeOpWarnings)");
		UnsafeOpWarnings.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.UNSAFE_OP_WARNINGS,project));

		safemath = new Button(composite,SWT.CHECK);
		safemath.setText("Report at compile-time (for constant expressions) and at run-time (in the generated code) integral arithmetic overflow [UNDER DEVELOPMENT] (--safemath)");
		safemath.setSelection(checkerProps.getBooleanProperty(JmlCheckerProperties.SAFE_MATH,project));
	}

	@Override
	protected void performDefaults() {
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);
		try {
			String admissValue = checkerProps.getDefaultProperty(JmlCheckerProperties.ADMISSIBILITY);
			if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_NONE)) {admissibility.select(0); }
			else if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_CLASSICAL)) {admissibility.select(1); }
			else if (admissValue.equalsIgnoreCase(JmlCheckerProperties.ADMISSIBILITY_OWNERSHIP)) {admissibility.select(2); }
			else {admissibility.select(0); } // hard coded default value

			/* String universexValue = checkerProps.getDefaultProperty(JmlCheckerProperties.UNIVERSESX);
			if (universexValue .equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_NO)) {universesx.select(0); }
			else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_PARSE)) {universesx.select(1); }
			else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_CHECK)) {universesx.select(2); }
			else if (universexValue.equalsIgnoreCase(JmlCheckerProperties.UNIVERSESX_FULL)) {universesx.select(3); }
			else {universesx.select(0); } // hard coded default value
			*/
			universesx.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.UNIVERSESX));

			classpath.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.CLASSPATH));
			destination.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.DESTINATION));
			excludeFiles.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.EXCLUDE_FILES));
			experiment.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.EXPERIMENT));
			filter.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.FILTER));
			xlint.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.XLINT));
			source.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.SOURCE));
			sourcePath.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.SOURCE_PATH));
			warning.setText(checkerProps.getDefaultProperty(JmlCheckerProperties.WARNING));

			Assignable.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.ASSIGNABLE));
			Quiet.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.QUIET));
			UnsafeOpWarnings.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.UNSAFE_OP_WARNINGS));
			assignable.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.aSSIGNABLE));
			debug.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.DEBUG));
			defaultNonNull.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.DEFAULT_NON_NULL));
			deprecation.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.DEPRECATION));
			generic.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.GENERIC));
			keepGoing.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.KEEP_GOING));
			multijava.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.MULTIJAVA));
			nonnull.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.NON_NULL));
			nonnulltypes.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.NON_NULL_TYPES));
			xArrayNNTS.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.XARRAY_NNTS));
			purity.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.PURITY));
			quiet.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.qUIET));
			recursive.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.RECURSIVE));
			relaxed.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.RELAXED));
			safemath.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.SAFE_MATH));
			verbose.setSelection(checkerProps.getBooleanDefaultProperty(JmlCheckerProperties.VERBOSE));
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
	}

	@Override
	public boolean performOk() {
		IProject p = getProject();
		try {
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.ASSIGNABLE), String.valueOf(assignable.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.QUIET), String.valueOf(Quiet.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.UNSAFE_OP_WARNINGS), String.valueOf(UnsafeOpWarnings.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.ADMISSIBILITY), admissibility.getItem(admissibility.getSelectionIndex()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.aSSIGNABLE), String.valueOf(assignable.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.CLASSPATH), classpath.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.DEBUG), String.valueOf(debug.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.DEFAULT_NON_NULL), String.valueOf(defaultNonNull.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.DEPRECATION), String.valueOf(deprecation.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.DESTINATION), destination.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.EXCLUDE_FILES), excludeFiles.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.EXPERIMENT), experiment.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.FILTER), filter.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.XLINT), xlint.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.GENERIC), String.valueOf(generic.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.KEEP_GOING), String.valueOf(keepGoing.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.MULTIJAVA), String.valueOf(multijava.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.NON_NULL), String.valueOf(nonnull.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.NON_NULL_TYPES), String.valueOf(nonnulltypes.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.XARRAY_NNTS), String.valueOf(xArrayNNTS.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.PURITY), String.valueOf(purity.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.qUIET), String.valueOf(quiet.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.RECURSIVE), String.valueOf(recursive.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.RELAXED), String.valueOf(relaxed.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.SAFE_MATH), String.valueOf(safemath.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.SOURCE), source.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.SOURCE_PATH), sourcePath.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.UNIVERSESX), universesx.getText());
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.VERBOSE), String.valueOf(verbose.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlCheckerProperties.WARNING), warning.getText());
		} catch (CoreException e) {
	          JmlPlugin.getDefault().getLog().log(
	                    new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.getMessage(), e));
			return false;
		}
		return true;
	}
}
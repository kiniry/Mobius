//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import jack.plugin.JackJml2bConfiguration;
import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.pog.Pog;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.util.FileUpdate;
import jml2b.util.ReplaceFileUpdate;
import jml2b.util.UpdatedJmlFile;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.contentmergeviewer.TextMergeViewer;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;

/**
 * Wizard allowing to select JML clause to generate, file when the automatic 
 * annotation is performed, view the difference between the new files and the old ones
 * and perform finally the modifications.
 * 
 * @author L. Burdy
 **/
public class AddJmlClauseWizard extends Wizard {

	IJml2bConfiguration config;
	LoadAndLink loadAndlinkAction;
	Vector generators;
	JmlFile jf;

	CheckboxTableViewer treeViewer;
	TextMergeViewer tmv;
	Vector fileUpdates;
	UpdatedJmlFile ds;

	IWizardPage loadAndLinkPage;
	IWizardPage selectMethodsPage;
	IWizardPage viewDiffsPage;
	IWizardPage noDiffPage;

	public AddJmlClauseWizard(
		ICompilationUnit cu,
		LoadAndLink loadAndlinkAction) {
		config = new JackJml2bConfiguration(cu.getJavaProject(), new JavaLoader());
		this.loadAndlinkAction = loadAndlinkAction;
		setNeedsProgressMonitor(true);
	}

	public boolean performFinish() {
		if (fileUpdates == null) {
			selectMethodsPage.getNextPage();
		}
		if (ds != null) {
			try {
				PrintStream os =
					new PrintStream(
						new BufferedOutputStream(
							new FileOutputStream(jf.getFileName().getFile())));
				LineNumberReader lnr =
					new LineNumberReader(
						new BufferedReader(
							new InputStreamReader(
								new FileInputStream(ds.getNewF()))));
				while (lnr.ready())
					os.println(lnr.readLine());
				lnr.close();
				os.close();
			} catch (IOException ioe) {
				return false;
			}
		}
		return true;
	}

	public void addPages() {
		loadAndLinkPage = new LoadAndLinkPage();
		addPage(loadAndLinkPage);
		selectMethodsPage = new SelectMethodsPage();
		addPage(selectMethodsPage);
		viewDiffsPage = new ViewDiffsPage();
		addPage(viewDiffsPage);
		noDiffPage = new NoDiffPage();
		addPage(noDiffPage);
	}

	public boolean canFinish() {
		return jf != null;
	}

	class LoadAndLinkPage extends WizardPage {

		Button modifies;
		Button requiresNullPointerE;
		Button requiresArrayOutOfBE;

		protected LoadAndLinkPage() {
			super("LoadAndLinkPage", "Select the JML clause to compute", null);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			modifies = new Button(c, SWT.CHECK);
			modifies.setSelection(true);
			modifies.setText("Compute modifies clauses");

			requiresNullPointerE = new Button(c, SWT.CHECK);
			requiresNullPointerE.setSelection(true);
			requiresNullPointerE.setText(
				"Compute requires clauses preventing from NullPointerException");

			requiresArrayOutOfBE = new Button(c, SWT.CHECK);
			requiresArrayOutOfBE.setSelection(true);
			requiresArrayOutOfBE.setText(
				"Compute requires clauses preventing from ArrayOutOfBoundsException");

			setControl(c);

		}

		public IWizardPage getNextPage() {
			try {
				getContainer().run(true, true, loadAndlinkAction);
			} catch (InvocationTargetException e) {
				Throwable t = e.getTargetException();
				Logger.err.println(
					"InvocationTargetException : " + t.toString());
				t.printStackTrace();
			} catch (Exception e) {
				return null;
			}
			treeViewer.setInput(jf = loadAndlinkAction.getJmlFile());
			treeViewer.setAllChecked(true);
			generators = new Vector();
			if (modifies.getSelection())
				generators.add(new ModifiesGenerator(config, getShell(), jf));
			if (requiresNullPointerE.getSelection()
				|| requiresArrayOutOfBE.getSelection())
				generators.add(
					new RequiresGenerator(
						config,
						getShell(),
						jf,
						requiresNullPointerE.getSelection(),
						requiresArrayOutOfBE.getSelection()));
			return selectMethodsPage;
		}

		public boolean canFlipToNextPage() {
			return isPageComplete();
		}

	}

	class SelectMethodsPage extends WizardPage {

		protected SelectMethodsPage() {
			super("SelectMethodsPage", "Select methods", null);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			Label l = new Label(c, SWT.NULL);
			l.setText("Select methods to compute");

			GridData gd = new GridData();
			gd.grabExcessHorizontalSpace = true;
			l.setLayoutData(gd);

			ViewForm treeForm = new ViewForm(c, SWT.BORDER);

			GridData gridData = new GridData();
			gridData.horizontalAlignment = GridData.FILL;
			gridData.verticalAlignment = GridData.FILL;
			gridData.grabExcessHorizontalSpace = true;
			gridData.grabExcessVerticalSpace = true;
			treeForm.setLayoutData(gridData);

			Table t = new Table(treeForm, SWT.CHECK);

			treeViewer = new CheckboxTableViewer(t);
			treeViewer.setContentProvider(new MethodListContentProvider());
			treeViewer.setLabelProvider(new MethodListLabelProvider());
			treeViewer.setInput(null);
			treeForm.setContent(treeViewer.getControl());
			setControl(c);
		}

		public IWizardPage getNextPage() {
			Object[] methods = treeViewer.getCheckedElements();
			try {
				Pog.init(config);
				Enumeration e = generators.elements();
				while (e.hasMoreElements()) {
					JmlClauseGenerator rwe =
						(JmlClauseGenerator) e.nextElement();
					rwe.setMethods(methods);
					getContainer().run(true, true, rwe);
				}
				Pog.end();

			} catch (InvocationTargetException e) {
				Throwable t = e.getTargetException();
				Logger.err.println(
					"InvocationTargetException : " + t.toString());
				t.printStackTrace();
			} catch (Exception e) {
				return null;
			}
			fileUpdates = new Vector();
			for (int i = 0; i < methods.length; i++) {
				Method m = (Method) methods[i];
				boolean updated = false;
				Enumeration e = generators.elements();
				while (e.hasMoreElements()) {
					JmlClauseGenerator rwe =
						(JmlClauseGenerator) e.nextElement();
					updated = updated || rwe.getUpdated(i);
				}
				if (updated) {
					fileUpdates.add(
						new ReplaceFileUpdate(
							m.getJmlFile().getFileName().getFile(),
							m.emitSpecCase(config),
							m.getFirstLine() - 1));
				}
			}
			try {
				Vector tmpfiles = FileUpdate.annotateFiles(fileUpdates);
				if (tmpfiles.size() > 0) {
					tmv.setInput(ds = (UpdatedJmlFile) tmpfiles.get(0));
					return viewDiffsPage;
				} else
					return noDiffPage;
			} catch (IOException ioe) {
				return noDiffPage;
			}
		}
		public boolean canFlipToNextPage() {
			return isPageComplete();
		}

	}

	class ViewDiffsPage extends WizardPage {

		protected ViewDiffsPage() {
			super("ViewDiffsPage", "Updates preview", null);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			ViewForm treeForm = new ViewForm(c, SWT.BORDER);
			GridData gridData = new GridData();
			gridData.horizontalAlignment = GridData.FILL;
			gridData.verticalAlignment = GridData.FILL;
			gridData.grabExcessHorizontalSpace = true;
			gridData.grabExcessVerticalSpace = true;
			treeForm.setLayoutData(gridData);

			tmv = new JmlMergeViewer(treeForm, new CompareConfiguration());
			tmv.setContentProvider(new JmlMergeViewerContentProvider());
			tmv.setInput(null);
			treeForm.setContent(tmv.getControl());
			setControl(c);
		}

		public boolean canFlipToNextPage() {
			return false;
		}

	}

	class NoDiffPage extends WizardPage {

		protected NoDiffPage() {
			super("NoDiffPage", "Updates preview", null);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			Label l = new Label(c, SWT.NULL);
			l.setText("No new clauses have been computed.");

			setControl(c);
		}

	}
}
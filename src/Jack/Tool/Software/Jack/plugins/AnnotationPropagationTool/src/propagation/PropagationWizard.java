//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package propagation;

import jack.plugin.JackJml2bConfiguration;
import jack.plugin.JackPlugin;
import jack.plugin.source.JmlMergeViewer;
import jack.plugin.source.JmlMergeViewerContentProvider;
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
import java.util.Iterator;
import java.util.Vector;

import jml2b.structure.java.JavaLoader;
import jml2b.util.UpdatedJmlFile;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.contentmergeviewer.TextMergeViewer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IParent;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.ui.JavaElementLabelProvider;
import org.eclipse.jdt.ui.StandardJavaElementContentProvider;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

/**
 *
 *  @author L. Burdy
 **/
public class PropagationWizard extends Wizard {

	private static final QualifiedName associatedUpdatedFiles =
		new QualifiedName("Annotation.Propagation", "AssocitedUpdatedFiles");

	JackJml2bConfiguration config;
	IFile propFile;
	Vector tmpFiles;

	TreeViewer treeViewer;
	TreeViewer updatedViewer;
	private UpdatedViewerFilter updatedViewerFilter;

	TextMergeViewer tmv;
	Vector fileUpdates;

	IWizardPage selectDestPage;
	IWizardPage viewDiffsPage;
	NoDiffPage noDiffPage;

	public PropagationWizard(IFile prop) {
		propFile = prop;
		config = new JackJml2bConfiguration(prop.getProject(), new JavaLoader());
		config.setDefaultExternalFile(true);
		setNeedsProgressMonitor(true);
	}

	public boolean performFinish() {
		if (tmpFiles == null) {
			selectDestPage.getNextPage();
		}
		Enumeration e = tmpFiles.elements();
		while (e.hasMoreElements()) {
			UpdatedJmlFile ujf = (UpdatedJmlFile) e.nextElement();

			try {
				PrintStream os =
					new PrintStream(
						new BufferedOutputStream(
							new FileOutputStream(ujf.getJf())));
				LineNumberReader lnr =
					new LineNumberReader(
						new BufferedReader(
							new InputStreamReader(
								new FileInputStream(ujf.getNewF()))));
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
		selectDestPage = new SelectDestPage();
		addPage(selectDestPage);
		viewDiffsPage = new ViewDiffsPage();
		addPage(viewDiffsPage);
		noDiffPage = new NoDiffPage();
		addPage(noDiffPage);
	}

	public boolean canFinish() {
		return selectDestPage.canFlipToNextPage();
	}

	class SelectDestPage extends WizardPage {

		Button modifies;
		Button requires;

		protected SelectDestPage() {
			super(
				"SelectDestPage",
				"Select the elements where the property will be propagated.",
				null);
			setPageComplete(false);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			Label l = new Label(c, SWT.NULL);
			l.setText("Select the target of the annotation propagation");

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

			treeViewer = new TreeViewer(treeForm, SWT.MULTI);
			treeViewer.setContentProvider(
				new StandardJavaElementContentProvider());
			treeViewer.setLabelProvider(new JavaElementLabelProvider());
			treeViewer.setInput(
				JavaCore.create(propFile.getWorkspace().getRoot()));
			treeViewer.addSelectionChangedListener(
				new MyTreeViewerSelectionChangedListener(this));
			treeForm.setContent(treeViewer.getControl());
			setControl(c);

		}

		public IWizardPage getNextPage() {
			config.setDefaultExternalFile(true);

			IStructuredSelection selectedElement =
				((IStructuredSelection) treeViewer.getSelection());

			Vector fis = new Vector();

			collectCompilationUnit(selectedElement, fis);

			PropagationGenerator pg =
				new PropagationGenerator(config, propFile, fis);

			try {
				getContainer().run(true, true, pg);
			} catch (InvocationTargetException e) {
				Throwable t = e.getTargetException();
				Logger.err.println( 
					"InvocationTargetException : " + t.toString());
				t.printStackTrace();
			} catch (InterruptedException e) {
				return noDiffPage;
			}

			if (!pg.hasSucceeded()) {
				MessageDialog.openInformation(
					getContainer().getShell(),
					JackPlugin.DIALOG_TITLE,
					pg.getErrorDescription());
				return noDiffPage;
			}

			tmpFiles = pg.getTmpFiles();
			if (tmpFiles.size() > 0) {
				updatedViewerFilter.setFilter(tmpFiles);
				updatedViewer.setInput(
					JavaCore.create(propFile.getWorkspace().getRoot()));
				return viewDiffsPage;
			} else
				return noDiffPage;
		}

		public boolean canFlipToNextPage() {
			return isPageComplete();
		}

		private void collectCompilationUnit(
			IStructuredSelection je,
			Vector res) {
			Iterator it = je.iterator();
			while (it.hasNext()) {
				IJavaElement element = (IJavaElement) it.next();
				collectCompilationUnit(element, res);
			}
		}

		private void collectCompilationUnit(IJavaElement je, Vector res) {
			if (je instanceof ICompilationUnit)
				res.add(je);
			else if (je instanceof IParent) {
				try {
					IJavaElement[] jes = ((IParent) je).getChildren();
					for (int i = 0; i < jes.length; i++)
						collectCompilationUnit(jes[i], res);
				} catch (JavaModelException jme) {
					Logger.err.println(jme.getMessage());
				}
			}
		}
	}

	class ViewDiffsPage extends WizardPage {

		protected ViewDiffsPage() {
			super("ViewDiffsPage", "Updates preview", null);
		}

		public void createControl(Composite parent) {
			SashForm c = new SashForm(parent, SWT.VERTICAL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			GridData gridData = new GridData();
			gridData.horizontalAlignment = GridData.FILL;
			gridData.verticalAlignment = GridData.FILL;
			gridData.grabExcessHorizontalSpace = true;
			gridData.grabExcessVerticalSpace = true;

			ViewForm listForm = new ViewForm(c, SWT.BORDER);
			listForm.setLayoutData(gridData);

			updatedViewer = new TreeViewer(listForm);
			updatedViewer.setContentProvider(
				new StandardJavaElementContentProvider());
			updatedViewer.setLabelProvider(new JavaElementLabelProvider());
			updatedViewer.setInput(
				JavaCore.create(propFile.getWorkspace().getRoot()));
			updatedViewerFilter = new UpdatedViewerFilter();
			updatedViewer.addFilter(updatedViewerFilter);
			listForm.setContent(updatedViewer.getControl());

			ViewForm treeForm = new ViewForm(c, SWT.BORDER);
			treeForm.setLayoutData(gridData);

			tmv = new JmlMergeViewer(treeForm, new CompareConfiguration());
			tmv.setContentProvider(new JmlMergeViewerContentProvider());
			tmv.setInput(null);
			treeForm.setContent(tmv.getControl());

			updatedViewer.addSelectionChangedListener(
				new JmlFileListSelectionChangedListener(tmv));

			setControl(c);
		}

		public boolean canFlipToNextPage() {
			return false;
		}

	}

	class NoDiffPage extends WizardPage {

		Label l;

		protected NoDiffPage() {
			super("NoDiffPage", "Updates preview", null);
		}

		public void createControl(Composite parent) {
			Composite c = new Composite(parent, SWT.NULL);
			GridLayout gridLayout = new GridLayout();
			gridLayout.marginWidth = 5;
			c.setLayout(gridLayout);

			l = new Label(c, SWT.NULL);
			l.setText("No new clauses have been computed.");

			setControl(c);
		}

	}

	class MyTreeViewerSelectionChangedListener
		implements ISelectionChangedListener {

		WizardPage wp;

		public MyTreeViewerSelectionChangedListener(WizardPage wp) {
			this.wp = wp;
		}

		public void selectionChanged(SelectionChangedEvent event) {
			wp.setPageComplete(
				event.getSelection() != null
					&& event.getSelection() instanceof IStructuredSelection
					&& !((IStructuredSelection) event.getSelection()).isEmpty());
		}

	}
	class JmlFileListSelectionChangedListener
		implements ISelectionChangedListener {

		TextMergeViewer tmv;

		public JmlFileListSelectionChangedListener(TextMergeViewer tmv) {
			this.tmv = tmv;
		}

		public void selectionChanged(SelectionChangedEvent event) {
			IJavaElement je =
				(IJavaElement) ((IStructuredSelection) event.getSelection())
					.getFirstElement();
			try {

				tmv.setInput(
					je.getResource().getSessionProperty(
						associatedUpdatedFiles));
			} catch (CoreException ce) {
				;
			}
		}

	}

	class JmlFileListLabelProvider extends LabelProvider {

		public String getText(Object element) {
			return ((UpdatedJmlFile) element).getJf().getName();
		}
	}

	class JmlFileListContentProvider implements IStructuredContentProvider {

		public Object[] getElements(Object inputElement) {
			return ((Vector) inputElement).toArray();
		}

		public void dispose() {
		}

		public void inputChanged(
			Viewer viewer,
			Object oldInput,
			Object newInput) {
		}

	}

	class UpdatedViewerFilter extends ViewerFilter {

		Vector tmpFiles = new Vector();

		boolean isVisible(IJavaElement je) {
			if (je instanceof ICompilationUnit) {
				Enumeration e = tmpFiles.elements();
				while (e.hasMoreElements()) {
					UpdatedJmlFile ujf = (UpdatedJmlFile) e.nextElement();
					if (ujf
						.getJf()
						.getAbsolutePath()
						.toString()
						.equals(je.getResource().getLocation().toString())) {
						try {
							je.getResource().setSessionProperty(
								associatedUpdatedFiles,
								ujf);
						} catch (CoreException ce) {
							return false;
						}
						return true;
					}
				}
				return false;
			} else if (
				je instanceof IJavaProject
					|| je instanceof IPackageFragment
					|| je instanceof IPackageFragmentRoot) {
				try {
					for (int i = 0;
						i < ((IParent) je).getChildren().length;
						i++)
						if (isVisible(((IParent) je).getChildren()[i]))
							return true;
				} catch (JavaModelException jme) {
					return false;
				}
			}
			return false;
		}

		public boolean select(
			Viewer viewer,
			Object parentElement,
			Object element) {
			return !tmpFiles.isEmpty()
				&& element instanceof IJavaElement
				&& isVisible((IJavaElement) element);
		}

		public void setFilter(Vector tmpFiles) {
			this.tmpFiles = tmpFiles;
		}

		public boolean isFilterProperty(Object element, String property) {
			return false;
		}

	}

}
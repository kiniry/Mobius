/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jack.plugin.metrics;

import jack.plugin.JackPlugin;
import jack.util.Logger;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.languages.Languages;
import jpov.Icons;
import jpov.PartialJpoFile;
import jpov.structure.Goal;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.printing.PrintDialog;
import org.eclipse.swt.printing.Printer;
import org.eclipse.swt.printing.PrinterData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IWorkbenchSite;
import org.eclipse.ui.part.ViewPart;

/**
 * View displaying the proof results of selected JML files.
 * 
 * @author L. Burdy
 */
public class MetricsView extends ViewPart {
	private TableViewer metricsViewer;
	private MetricsFilterWindow filterw;

	private ICompilationUnit current;

	public MetricsView() {
		;
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchPart#createPartControl(Composite)
	 */
	public void createPartControl(Composite parent) {
		createTable(parent);
		createMenus();
	}

	/*@
	  @ requires proofViewer != null;
	  @*/
	private void addColumn(
		MetricsLabelProvider proof_provider,
		MetricsColumnProvider provider) {
		TableColumn tmp = new TableColumn(metricsViewer.getTable(), SWT.CENTER);
		tmp.setText(provider.getLabel());
		tmp.setWidth(provider.getDefaultWidth());
		proof_provider.add(provider);
	}

	private void createTable(Composite parent) {
		Table table =
			new Table(
				parent,
				SWT.H_SCROLL
					| SWT.V_SCROLL
					| SWT.BORDER
					| SWT.MULTI
					| SWT.FULL_SELECTION);

		metricsViewer = new TableViewer(table);
		MetricsLabelProvider provider = new MetricsLabelProvider();

		addColumn(provider, new ProofFileLabelProvider());
		addColumn(provider, new POCountLabelProvider());
		addColumn(provider, new POProvedLabelProvider());
		addColumn(provider, new PercentProvedLabelProvider());
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String element = (String) e.nextElement();
			if (Languages.getProverStatusClass(element) != null)
				addColumn(provider, new ProverPOProvedLabelProvider(element));

		}

		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		filterw = new MetricsFilterWindow(getSite().getShell(), this);

		metricsViewer.setContentProvider(new MetricsContentProvider(filterw));
		metricsViewer.setLabelProvider(provider);
		metricsViewer.setInput(null);
	}

	/*@
	  @ requires proofViewer != null;
	  @*/
	private void createMenus() {
		FilterAction filter = new FilterAction(filterw);

		PrintDialog pd = new PrintDialog(getSite().getShell(), SWT.NULL);
		pd.open();
		PrinterAction printer = new PrinterAction(pd);

		// add the actions to the toolbar
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager toolbar = bars.getToolBarManager();
		toolbar.add(filter);
		toolbar.add(printer);
	}

	public void dispose() {
	}

	void refresh() {
		if (current != null)
			setContent(current);
	}

	void setContent(ICompilationUnit c) {
		current = c;
		switch (filterw.getFilterType()) {
			case MetricsFilterWindow.PROJECT :
				IJavaElement jf = c.getParent();
				while (!(jf instanceof IJavaProject))
					jf = jf.getParent();
				metricsViewer.setInput(jf);
			case MetricsFilterWindow.PACKAGE :
				metricsViewer.setInput(c.getParent());
				break;
			case MetricsFilterWindow.RESSOURCE_ONLY :
				metricsViewer.setInput(c);
				break;
			default :
				}
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchPart#setFocus()
	 */
	public void setFocus() {
	}

}

/**
 * A class that uses an <code>ILabelProvider</code> for each of the 
 * columns of the table.
 */
class MetricsLabelProvider
	extends LabelProvider
	implements ITableLabelProvider {
	private Vector columnProviders;

	public MetricsLabelProvider() {
		columnProviders = new Vector();
	}

	/**
	 * Adds a label providers for a new column.
	 */
	public void add(ILabelProvider c) {
		columnProviders.add(c);
	}

	public Image getColumnImage(Object element, int column_index) {
		if (column_index < columnProviders.size()) {
			ILabelProvider provider =
				(ILabelProvider) columnProviders.get(column_index);
			return provider.getImage(element);
		} else {
			return null;
		}
	}

	public String getColumnText(Object element, int column_index) {
		if (column_index < columnProviders.size()) {
			ILabelProvider provider =
				(ILabelProvider) columnProviders.get(column_index);
			return provider.getText(element);
		} else {
			return "Error: MetricsLabelProvider.getColumnText() : column_index >= columnProviders.size()";
		}
	}
}

/**
 * This class provides the name of a JML file.
 *
 *  @author L. Burdy
 **/
class ProofFileLabelProvider extends MetricsColumnProvider {
	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}
	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		return c.getElementName();
	}

	public String getLabel() {
		return "File";
	}

	public int getDefaultWidth() {
		return 128;
	}

	public String getTextForGoal(Goal g) {
		return g.getText(0);
	}
}

/**
 * This class provides the number of proof obligation of a JML file.
 *
 *  @author L. Burdy
 **/
class POCountLabelProvider extends MetricsColumnProvider {
	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}

	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		if (jpo == null)
			return "";
		return jpo.getPartialJmlFile().getNbPo() + "";
	}

	public String getLabel() {
		return "PO";
	}

	public int getDefaultWidth() {
		return 128;
	}

	public String getTextForGoal(Goal g) {
		return "-";
	}
}

/**
 * This class provides the global proof percentage of a JML file.
 *
 *  @author L. Burdy
 **/
class PercentProvedLabelProvider extends MetricsColumnProvider {
	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}

	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		if (jpo == null)
			return "";
		int po = jpo.getPartialJmlFile().getNbPo();
		po =
			(po == 0)
				? 100
				: (jpo.getPartialJmlFile().getNbPoProved() * 100 / po);
		return po + "";
	}

	public String getLabel() {
		return "%";
	}

	public int getDefaultWidth() {
		return 128;
	}

	public String getTextForGoal(Goal g) {
		return "-";
	}
}

/**
 * This class provides the number of proved proof obligation of a JML file.
 *
 *  @author L. Burdy
 **/
class POProvedLabelProvider extends MetricsColumnProvider {
	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}
	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		if (jpo == null)
			return "";
		return jpo.getPartialJmlFile().getNbPoProved() + "";
	}

	public String getLabel() {
		return "Proved";
	}

	public int getDefaultWidth() {
		return 128;
	}

	public String getTextForGoal(Goal g) {
		return g.isProved() ? "1" : "0";
	}
}

/**
 * This class provides the number of proved proof obligation by a given prover of 
 * a JML file.
 *
 *  @author L. Burdy
 **/
class ProverPOProvedLabelProvider extends MetricsColumnProvider {
	String prover;

	ProverPOProvedLabelProvider(String p) {
		prover = p;
	}

	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}

	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		if (jpo == null)
			return "";
		return jpo.getPartialJmlFile().getNbPOProved(prover) + "";
	}

	public String getLabel() {
		return prover;
	}

	public int getDefaultWidth() {
		return 128;
	}

	public String getTextForGoal(Goal g) {
		return g.isProved(prover) ? "1" : "0";
	}
}

/**
 * This class provides the compiled state of a JML file.
 *
 *  @author L. Burdy
 **/
class TextStateLabelProvider extends MetricsColumnProvider {

	IWorkbenchSite site;

	TextStateLabelProvider(IWorkbenchSite site) {
		this.site = site;
	}

	public Image getImage(ICompilationUnit c, PartialJpoFile jpo) {
		return null;
	}

	public String getText(ICompilationUnit c, PartialJpoFile jpo) {
		try {
			if (c.getResource().getPersistentProperty(JackPlugin.JML_COMPILED)
				== null
				|| c.getResource().getPersistentProperty(
					JackPlugin.JML_COMPILED).equals(
					"false"))
				return "_";

			return "COMPILED";
		} catch (CoreException ce) {
			MessageDialog.openError(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + ce.getMessage());
			return "_";
		}

	}

	public String getLabel() {
		return "State";
	}

	public int getDefaultWidth() {
		return 64;
	}

	public String getTextForGoal(Goal g) {
		return "-";
	}
}

/**
 * Convenience class allowing to define label providers for <code>ProofTask</code>
 * elements without casting <code>Object</code>s into <code>ProofTask</code>s.
 */
abstract class MetricsColumnProvider extends LabelProvider {

	/**
	 * Returns the label corresponding to this <code>ProofTaskLabelProvider</code>.
	 * The label correspond to the text that should be displayed in the 
	 * column header.
	 */
	abstract public String getLabel();

	/**
	 * Method called for providing images for the given <code>ProofTask</code>
	 * object.
	 */
	abstract public Image getImage(ICompilationUnit c, PartialJpoFile jpo);

	/**
	 * Method called for providing label for the given <code>ProofTask</code>
	 * object.
	 */
	abstract public String getText(ICompilationUnit c, PartialJpoFile jpo);

	abstract public String getTextForGoal(Goal g);

	/**
	 * Implementation of <code>LabelProvider.getImage()</code>.
	 * 
	 * It casts the <code>Object</code> parameter into a <code>ProofTask</code>
	 * object and calls <code>getImage(ProofTask)</code>.
	 */
	public Image getImage(Object o) {
		if (o instanceof ICompilationUnit) {
		PartialJpoFile jpo = PartialJpoFile.getJpo((ICompilationUnit) o);
		return getImage((ICompilationUnit) o, jpo);
		}
		else return null;
	}

	/**
	 * Implementation of <code>LabelProvider.getText()</code>.
	 * 
	 * It casts the <code>Object</code> parameter into a <code>ProofTask</code>
	 * object and calls <code>getText(ProofTask)</code>.
	 */
	public String getText(Object o) {
		if (o instanceof ICompilationUnit) {
			PartialJpoFile jpo = PartialJpoFile.getJpo((ICompilationUnit) o);
			return getText((ICompilationUnit) o, jpo);
		} else
			return getTextForGoal((Goal) o);
	}

	/**
	 * Should return a column width appropriate for a <code>TableViewer</code>.
	 */
	public abstract int getDefaultWidth();
}

/**
 * This action prints the content of the view
 *
 *  @author L. Burdy
 **/
class PrinterAction extends Action {

	MetricsFilterWindow mfw;
	PrintDialog pd;

	PrinterAction(PrintDialog pd) {
		this.pd = pd;
		setText("Printer");
		setToolTipText("Print the table");
		setImageDescriptor(Icons.PRINTER_DESCRIPTOR);
	}

	public void run() {
		PrinterData data = pd.open();
		if (data == null) {
			Logger.get().println("Warning: No default printer.");
			return;
		}
		Logger.get().println(data.toString());
		Printer printer = new Printer();
		if (printer.startJob("SWT Printing Snippet")) {
			Color black = printer.getSystemColor(SWT.COLOR_BLACK);
			Color white = printer.getSystemColor(SWT.COLOR_WHITE);
			Color red = printer.getSystemColor(SWT.COLOR_RED);
			Rectangle trim = printer.computeTrim(0, 0, 0, 0);
			Point dpi = printer.getDPI();
			int leftMargin = dpi.x + trim.x;
			// one inch from left side of paper
			int topMargin = dpi.y / 2 + trim.y;
			// one-half inch from top edge of paper
			GC gc = new GC(printer);
			Font font = gc.getFont();
			// example just uses printer's default font
			if (printer.startPage()) {
				gc.setBackground(white);
				gc.setForeground(black);
				String testString = "Hello World!";
				Point extent = gc.stringExtent(testString);
				gc.drawString(
					testString,
					leftMargin,
					topMargin + font.getFontData()[0].getHeight());
				gc.setForeground(red);
				gc.drawRectangle(leftMargin, topMargin, extent.x, extent.y);
				printer.endPage();
			}
			gc.dispose();
			printer.endJob();
		}
		printer.dispose();
	}
}

/**
 * This action opens the metrics filter window.
 *
 *  @author L. Burdy
 **/
class FilterAction extends Action {

	MetricsFilterWindow mfw;

	FilterAction(MetricsFilterWindow mfw) {
		this.mfw = mfw;
		setText("Filter");
		setToolTipText("Filter the displayed java file");
		setImageDescriptor(Icons.FILTER_DESCRIPTOR);
	}

	public void run() {
		mfw.open();
	}
}

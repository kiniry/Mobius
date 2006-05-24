//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProofView.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.prove;

import jack.plugin.JackPlugin;

import java.text.DateFormat;
import java.util.Date;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Locale;
import java.util.Vector;

import jml2b.languages.Languages;
import jpov.Icons;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.part.ViewPart;

/**
 * View that allows controling and showing proof tasks.
 * 
 * @author A. Requet, L. Burdy
 */
public class ProofView extends ViewPart {
	private TableViewer proofViewer;

	public void freezeNotify() {
		proofTasks.freezeNotify();
	}

	public void unfreezeNotify() {
		proofTasks.unfreezeNotify();
	}

	/**
	 * Action allowing to remove the selected element.
	 */
	private Action removeSelected;

//	/** 
//	 * Action allowing starting the selected task.
//	 */
//	private Action startSelected;

	/**
	 * Action allowing to remove all the finished tasks.
	 */
	private Action removeFinished;

	private Action removeAll;
	
	private Action recompile;
	
	private Action edit;

	/**
	 * List of proof tasks that should be performed.
	 */
	private ProofTaskList proofTasks;

	private static ProofView curr;

	public static ProofView getCurrent(){
		return curr;
	}
	
	public ProofView() {
		proofTasks = new ProofTaskList(JackPlugin.getMaxProofRunning());
		proofTasks.start();
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchPart#createPartControl(Composite)
	 */
	public void createPartControl(Composite parent) {
		// ensures that the images are loaded
		//    	EclipseJpov.initImages(JackPlugin.getIconDir());
		createTable(parent);

		createMenus();

		proofViewer.addDoubleClickListener(new ProofClickListener());
	}

	/*@
	  @ requires proofViewer != null;
	  @*/
	private void addColumn(
		ProofLabelProvider proof_provider,
		ProofTaskLabelProvider provider) {
		TableColumn tmp = new TableColumn(proofViewer.getTable(), SWT.CENTER);
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

		proofViewer = new TableViewer(table);
		ProofLabelProvider provider = new ProofLabelProvider();

		addColumn(provider, new ImageStateLabelProvider());
		addColumn(provider, new ProofFileLabelProvider());
		addColumn(provider, new TextStateLabelProvider());
		addColumn(provider, new ProverLabelProvider());
		addColumn(provider, new POCountLabelProvider());
		addColumn(provider, new POTriedLabelProvider());
		addColumn(provider, new POProvedLabelProvider());
		addColumn(provider, new PercentTriedLabelProvider());
		addColumn(provider, new PercentProvedLabelProvider());
		addColumn(provider, new CreationDateLabelProvider());
		addColumn(provider, new StartDateLabelProvider());
		addColumn(provider, new EndDateLabelProvider());
		addColumn(provider, new ElapsedTimeLabelProvider());

		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		proofViewer.setContentProvider(new ProofContentProvider());
		proofViewer.setLabelProvider(provider);
		proofViewer.setInput(proofTasks);
	}

	/*@
	  @ requires proofViewer != null;
	  @*/
	private void createMenus() {
		IActionBars bars = getViewSite().getActionBars();
		IMenuManager menu = bars.getMenuManager();

		removeSelected = new RemoveSelectedAction();
		removeFinished = new RemoveFinishedAction();
		removeAll = new RemoveAllAction();
		recompile = new RecompileAction();
		edit = new EditAction();
//		startSelected = new StartSelectedAction();

		menu.add(removeSelected);
		menu.add(removeFinished);

		// add the actions to the toolbar
		IToolBarManager toolbar = bars.getToolBarManager();
		//toolbar.add(removeSelected);
		toolbar.add(removeFinished);

		// creates the context menu        
		MenuManager menu_manager = new MenuManager();

//		menu_manager.add(startSelected);
		menu_manager.add(new Separator());
		menu_manager.add(removeSelected);
		menu_manager.add(removeFinished);
		menu_manager.add(removeAll);
		menu_manager.add(recompile);
		menu_manager.add(edit);
		
		MenuManager subMenu = new MenuManager("Prove");
		menu_manager.add(subMenu);
		
		Enumeration e = Languages.getProofTaskClasses();
		while (e.hasMoreElements()) {
			ProofTask pt = (ProofTask) e.nextElement();
			if (pt != null)
			subMenu.add(new ProveAction(pt));
		}

		// Create menu.
		Menu ctx_menu = menu_manager.createContextMenu(proofViewer.getTable());
		proofViewer.getTable().setMenu(ctx_menu);

	}

	public void dispose() {
		// try to stop all the threads.
		proofTasks.stopAll();
		proofTasks.stopPlease();
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchPart#setFocus()
	 */
	public void setFocus() {
	}

	/**
	 * Adds the given proof to the list of proofs to be performed.
	 */
	public void addProof(ProofTask tsk) {
		proofTasks.add(tsk);
	}

	class RemoveSelectedAction extends Action {
		RemoveSelectedAction() {
			setText("Terminate");
			setToolTipText("Terminates the selected element");
			setImageDescriptor(Icons.REMOVE_TASK_DESCRIPTOR);
		}

		public void run() {
			IStructuredSelection sel =
				(IStructuredSelection) proofViewer.getSelection();

			if (sel.isEmpty()) {
				return;
			}

			Iterator i = sel.iterator();
			while (i.hasNext()) {
				ProofTask tsk = (ProofTask) i.next();
				// removes the task
				proofTasks.remove(tsk);
			}
			// proofTasks.removeAll(sel.toList());
			proofViewer.refresh();
		}
	}

	class RecompileAction extends Action {
		RecompileAction() {
			setText("Verify");
			setToolTipText("Generates cases for the selected element");
			setImageDescriptor(Icons.REMOVE_TASK_DESCRIPTOR);
		}

		public void run() {
			IStructuredSelection sel =
				(IStructuredSelection) proofViewer.getSelection();

			if (sel.isEmpty()) {
				return;
			}

			Iterator i = sel.iterator();
			while (i.hasNext()) {
				ProofTask tsk = (ProofTask) i.next();
				// removes the task
				proofTasks.recompile(tsk);
			}
			// proofTasks.removeAll(sel.toList());
			proofViewer.refresh();
		}
	}

	class EditAction extends Action {
		EditAction() {
			setText("Edit");
			setToolTipText("Edit the selected element");
			setImageDescriptor(Icons.REMOVE_TASK_DESCRIPTOR);
		}

		public void run() {
			IStructuredSelection sel =
				(IStructuredSelection) proofViewer.getSelection();

			if (sel.isEmpty()) {
				return;
			}

			Iterator i = sel.iterator();
			while (i.hasNext()) {
				ProofTask tsk = (ProofTask) i.next();
				// removes the task
				proofTasks.edit(tsk);
			}
			// proofTasks.removeAll(sel.toList());
			proofViewer.refresh();
		}
	}

	class ProveAction extends Action {
		ProofTask pt;
		
		ProveAction(ProofTask pt) {
			this.pt = pt;
			setText(pt.getProverName());
			setToolTipText("Prove the selected element");
			setImageDescriptor(Icons.REMOVE_TASK_DESCRIPTOR);
		}

		public void run() {
			IStructuredSelection sel =
				(IStructuredSelection) proofViewer.getSelection();

			if (sel.isEmpty()) {
				return;
			}

			Iterator i = sel.iterator();
			while (i.hasNext()) {
				ProofTask tsk = (ProofTask) i.next();
				// removes the task
				proofTasks.reprove(tsk, pt);
			}
			// proofTasks.removeAll(sel.toList());
			proofViewer.refresh();
		}
	}

//	class StartSelectedAction extends Action {
//		StartSelectedAction() {
//			setText("Start");
//			setToolTipText("Starts the selected element");
//			setImageDescriptor(EclipseJpov.TASK_RUNNING_DESCRIPTOR);
//		}
//
//		public void run() {
//			IStructuredSelection sel =
//				(IStructuredSelection) proofViewer.getSelection();
//
//			if (sel.isEmpty()) {
//				return;
//			}
//
//			Iterator i = sel.iterator();
//			while (i.hasNext()) {
//				ProofTask tsk = (ProofTask) i.next();
//				// starts the task
//				proofTasks.startProof(tsk);
//			}
//			// proofTasks.removeAll(sel.toList());
//			proofViewer.refresh();
//		}
//	}

	class RemoveFinishedAction extends Action {
		RemoveFinishedAction() {
			setText("Remove finished");
			setToolTipText("Removes the finished proof tasks");
			setImageDescriptor(Icons.REMOVE_ALL_TASKS_DESCRIPTOR);
		}

		public void run() {
			proofTasks.removeFinished();
		}
	}

	class RemoveAllAction extends Action {
		RemoveAllAction() {
			setText("Remove all");
			setToolTipText("Removes all the non running proof tasks");
			setImageDescriptor(Icons.REMOVE_ALL_TASKS_DESCRIPTOR);
		}

		public void run() {
			proofTasks.removeAll();
		}
	}

}

/**
 * A class that uses an <code>ILabelProvider</code> for each of the 
 * columns of the table.
 */
class ProofLabelProvider extends LabelProvider implements ITableLabelProvider {
	private Vector columnProviders;

	public ProofLabelProvider() {
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
			return "Error: ProofLabelProvider.getColumnText() : column_index >= columnProviders.size()";
		}
	}
}

/**
 * Convenience class allowing to define label providers for <code>ProofTask</code>
 * elements without casting <code>Object</code>s into <code>ProofTask</code>s.
 */
abstract class ProofTaskLabelProvider extends LabelProvider {

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
	abstract public Image getImage(ProofTask tsk);

	/**
	 * Method called for providing label for the given <code>ProofTask</code>
	 * object.
	 */
	abstract public String getText(ProofTask tsk);

	/**
	 * Implementation of <code>LabelProvider.getImage()</code>.
	 * 
	 * It casts the <code>Object</code> parameter into a <code>ProofTask</code>
	 * object and calls <code>getImage(ProofTask)</code>.
	 */
	public Image getImage(Object o) {
		return getImage((ProofTask) o);
	}

	/**
	 * Implementation of <code>LabelProvider.getText()</code>.
	 * 
	 * It casts the <code>Object</code> parameter into a <code>ProofTask</code>
	 * object and calls <code>getText(ProofTask)</code>.
	 */
	public String getText(Object o) {
		return getText((ProofTask) o);
	}

	/**
	 * Should return a column width appropriate for a <code>TableViewer</code>.
	 */
	public abstract int getDefaultWidth();
}

/**
 * Label provider that provides an image corresponding to the state
 * of the proof task (<code>RUNNING</code>, <code>FINISHED</code> or
 * <code>WAITING</code>.
 * <p>
 * This label provider does not provides text.
 */
class ImageStateLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		switch (tsk.getCurrentState()) {
			case ProofTask.RUNNING :
			case ProofTask.LOADING :
				return Icons.TASK_RUNNING;
			case ProofTask.FINISHED :
			case ProofTask.STOPPED :
			case ProofTask.ERROR :
				return Icons.TASK_FINISHED;
			case ProofTask.WAITING :
				return Icons.TASK_WAITING;
		}
		return null;
	}

	public String getText(ProofTask task) {
		return "";
	}

	public String getLabel() {
		return " ";
	}

	public int getDefaultWidth() {
		return 24;
	}
}

class TextStateLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}

	public String getText(ProofTask tsk) {
		switch (tsk.getCurrentState()) {
			case ProofTask.RUNNING :
				return "RUNNING";
			case ProofTask.FINISHED :
				return "FINISHED";
			case ProofTask.STOPPED :
				return "STOPPED";
			case ProofTask.WAITING :
				return "WAITING";
			case ProofTask.ERROR :
				return "ERROR";
			case ProofTask.LOADING :
				return "LOADING";
			default :
				return "UNKNOWN";
		}
	}

	public String getLabel() {
		return "Status";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class ProverLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}

	public String getText(ProofTask tsk) {
		return tsk.getProverName();
	}

	public String getLabel() {
		return "Prover";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class ProofFileLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		return tsk.getFileName();
	}

	public String getLabel() {
		return "File";
	}

	public int getDefaultWidth() {
		return 128;
	}
}

class POCountLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		int nb_po = tsk.nbPo();
		return nb_po >= 0 ? Integer.toString(tsk.nbPo()) : "-";
	}

	public String getLabel() {
		return "PO Count";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class POTriedLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		int po_tried = tsk.getPoTried();

		return po_tried >= 0 ? Integer.toString(tsk.getPoTried()) : "-";
	}

	public String getLabel() {
		return "PO Tried";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class POProvedLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		int tmp = tsk.getPoProved();
		return tmp >= 0 ? Integer.toString(tsk.getPoProved()) : "-";
	}

	public String getLabel() {
		return "PO Proved";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class PercentTriedLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		// number of proof obligations that have been tried
		int tried = tsk.getPoTried();
		int po_count = tsk.getNumToTry();

		if (tried <= 0 || po_count <= 0) {
			return "-";
		}

		if (tried == po_count) {
			return "100";
		}
		int result = tried * 100 / po_count;
		return Integer.toString(result);
	}

	public String getLabel() {
		return "% Tried";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class PercentProvedLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		int pos = tsk.nbPo();
		if (pos < 0) {
			return "-";
		}
		if (pos == 0) {
			return "100";
		}
		int result = tsk.getPoProved() * 100 / pos;
		return Integer.toString(result);
	}

	public String getLabel() {
		return "% Proved";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class CreationDateLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		return DateFormat.getTimeInstance(
			DateFormat.DEFAULT,
			Locale.FRANCE).format(
			tsk.getCreationDate());

	}

	public String getLabel() {
		return "Added";
	}

	public int getDefaultWidth() {
		return 128;
	}
}

class StartDateLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		Date d = tsk.getStartDate();
		if (d != null) {
			return DateFormat.getTimeInstance(
				DateFormat.DEFAULT,
				Locale.FRANCE).format(
				d);
		} else {
			return "-";
		}
	}

	public String getLabel() {
		return "Started";
	}

	public int getDefaultWidth() {
		return 128;
	}
}

class ElapsedTimeLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		Date start = tsk.getStartDate();
		Date end = tsk.getEndDate();
		if (end == null) {
			return "-";
		}

		long start_millis, end_millis;

		start_millis = start.getTime();
		end_millis = end.getTime();

		long elapsed = end_millis - start_millis;

		return Long.toString(elapsed / 1000) + " seconds";
	}

	public String getLabel() {
		return "Elapsed time";
	}

	public int getDefaultWidth() {
		return 64;
	}
}

class EndDateLabelProvider extends ProofTaskLabelProvider {
	public Image getImage(ProofTask tsk) {
		return null;
	}
	public String getText(ProofTask tsk) {
		Date d = tsk.getEndDate();
		if (d != null) {
			return DateFormat.getTimeInstance(
				DateFormat.DEFAULT,
				Locale.FRANCE).format(
				d);
		} else {
			return "-";
		}
	}

	public String getLabel() {
		return "Finished";
	}

	public int getDefaultWidth() {
		return 128;
	}
}

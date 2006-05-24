//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LemmaFilterWindow.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import jpov.structure.Class;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/**
 * This class displays the filter window that allow to filter hypotheses
 * @author L. Burdy, A. Requet
 **/
public class LemmaFilterWindow extends Dialog {

	/**
	 * This array contains ordered hypothese type.
	 **/
	private String[] showTypes;
	
	/**
	 * The displayed list of all hypothese types
	 **/
	private List hypTypeList;

	private Button[] fields;

	private Vector selectedFields = new Vector();

	private Button selectField;

	private boolean isFieldselected = false;

	private CTabFolder tabFold;

	private int selectedTab = 0;

	private Text otherFields;

	private String otherFieldsList = "";

	//@ selectedFields.elementType == \type(Field);

	/**
	 * The set of hypothesis viewers
	 **/
	private Hashtable hypViewers;

	private Class currentClass;

	/**
	 * Constructs a filter window into the current shell.
	 * @param parent The current shell
	 **/
	public LemmaFilterWindow(Shell parent, Hashtable hypViewers) {
		super(parent);
		this.hypViewers = hypViewers;
		showTypes = new String[jml2b.pog.lemma.VirtualFormula.getMaxHypType()];

		for (byte i = 0;
			i < jml2b.pog.lemma.VirtualFormula.getMaxHypType();
			i++)
			showTypes[i] = jml2b.pog.lemma.VirtualFormula.getHypTypeString(i);
	}

	/**
	 * Displays the list of hypothese types.
	 **/
	protected Control createDialogArea(Composite parent) {
		tabFold = new CTabFolder(parent, SWT.BOTTOM);
		CTabItem ti = new CTabItem(tabFold, 0);
		ti.setText("Origin");
		Composite c1 = new Composite(tabFold, SWT.NULL);
		ti.setControl(c1);

		GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		c1.setLayout(gridLayout);

		GridData data;
		Label l = new Label(c1, SWT.NULL);
		l.setText("Select sorting of hypothesis");
		data = new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = true;
		data.horizontalSpan = 2;
		l.setLayoutData(data);

		hypTypeList = new List(c1, SWT.SINGLE | SWT.BORDER);
		data = new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = true;
		data.horizontalSpan = 1;
		data.verticalSpan = 5;
		hypTypeList.setLayoutData(data);

		hypTypeList.setItems(showTypes);

		Button moveUp = new Button(c1, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		moveUp.setLayoutData(data);
		moveUp.setText("Up");
		moveUp.addSelectionListener(new MoveElementListener(-1));

		Button moveDown = new Button(c1, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		moveDown.setLayoutData(data);
		moveDown.setText("Down");
		moveDown.addSelectionListener(new MoveElementListener(+1));

		ti = new CTabItem(tabFold, 1);
		ti.setText("Fields");

		c1 = new Composite(tabFold, SWT.NULL);
		ti.setControl(c1);

		gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		c1.setLayout(gridLayout);

		selectField = new Button(c1, SWT.CHECK);
		selectField.setText("Select fields occuring in hypothesis to display");
		selectField.setSelection(isFieldselected);
		if (currentClass != null) {
			fields = new Button[currentClass.getFields().length];
			for (int i = 0; i < currentClass.getFields().length; i++) {
				fields[i] = new Button(c1, SWT.CHECK);
				fields[i].setText(currentClass.getFields()[i].getName());
				if (selectedFields
					.contains(currentClass.getFields()[i].getName()))
					fields[i].setSelection(true);
				fields[i].setEnabled(isFieldselected);
			}
		}

		l = new Label(c1, SWT.NULL);
		l.setText("Comma separated list of other variables");

		otherFields = new Text(c1, SWT.BORDER);
		otherFields.setEnabled(isFieldselected);
		otherFields.setText(otherFieldsList);

		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		otherFields.setLayoutData(gridData);

		selectField.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				otherFields.setEnabled(selectField.getSelection());
				for (int i = 0; i < currentClass.getFields().length; i++)
					fields[i].setEnabled(selectField.getSelection());
			}
		});

		tabFold.setSelection(selectedTab);
		return tabFold;
	}

	/**
	 * Updates the <code>showTypes</code> field depending on the selected 
	 * items in the list. Refreshes the hypothesis viewers
	 **/
	protected void okPressed() {
		showTypes= hypTypeList.getItems();

		isFieldselected = selectField.getSelection();
		selectedFields = new Vector();
		if (isFieldselected) {
			for (int i = 0; i < fields.length; i++)
				if (fields[i].getSelection())
					selectedFields.add(fields[i].getText());
			otherFieldsList = otherFields.getText();
			String[] s = jml2b.util.Util.tokenize(otherFieldsList, ",");
			for (int i = 0; i < s.length; i++)
				selectedFields.add(s[i]);
		}

		// refreshes all the hypothesis viewers
		Enumeration e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			t.refresh();
		}

		selectedTab = tabFold.getSelectionIndex();

		setReturnCode(Window.OK);
		close();
	}

	/**
	 * @param class1
	 */
	public void setCurrentClass(Class class1) {
		currentClass = class1;
	}

	private int getPosition(byte origin) {
		for (int i = 0; i < showTypes.length; i++)
			if (jml2b
				.pog
				.lemma
				.VirtualFormula
				.getHypTypeString(origin)
				.equals(showTypes[i]))
				return i;
		return -1;
	}

	/**
	 * @param h1
	 */
	public int isShow(HypLine h1) {
		if (!isFieldselected)
			return getPosition(h1.getOrigin());
		else
			return -h1.getFormula().contains(selectedFields);

	}

	/**
	 * <code>SelectionListener</code> allowing to move elements up or down
	 * in the list.
	 * <p>
	 * Note that the direction of the <code>SelectionListener</code> is 
	 * defined at creation time. Thus, if it is needed to move elements up
	 * and down, two different <code>MoveElementListener</code> have to be 
	 * used.
	 */
	class MoveElementListener implements SelectionListener {
		/** 
		 * The relative displacement of the selected element. 
		 * The widgetSelected method will move the selected element of 
		 * <code>delta</code> positions in the list.
		 * <p>
		 * Typical values for <code>delta</code> would be 1 or -1.
		 */
		private int delta;

		public MoveElementListener(int delta) {
			this.delta = delta;
		}

		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			// get index of selected element
			int selected = hypTypeList.getSelectionIndex();

			if (selected == -1) {
				// abort if no item is selected
				return;
			}

			int count = hypTypeList.getItemCount();

			// ensures that the element can be moved
			int destination = selected + delta;
			if (destination >= count || destination < 0) {
				// element cannot be moved
				return;
			}

			// moves the selected element. this is performed by removing the
			// element, and adding it at the destination position
			String element = hypTypeList.getItem(selected);
			hypTypeList.remove(selected);
			hypTypeList.add(element, destination);
			hypTypeList.select(destination);
		}
	}

}

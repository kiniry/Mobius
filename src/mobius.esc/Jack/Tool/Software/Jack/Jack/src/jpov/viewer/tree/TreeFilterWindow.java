//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeFilterWindow.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jack.plugin.perspective.ICaseExplorer;
import jml2b.pog.lemma.GoalOrigin;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/**
 * This class implements the dialog that displays the window allowing to 
 * choose the filter to apply to the tree
 * @author L. Burdy, A. Requet
 **/
public class TreeFilterWindow extends Dialog {

	/**
	 * Indicates whether the proved items must be display or not.
	 **/
	private boolean showProved = false;

	/**
	 * Indicates whether the unproved items must be display or not.
	 **/
	private boolean showUnProved = true;

	/**
	 * Upper proof percentage bound for a class to be displayed 
	 **/
	private int classPercent = 100;

	/**
	 * Upper proof percentage bound for a method to be displayed 
	 **/
	private int methodPercent = 99;

	/**
	 * Upper proof percentage bound for a case to be displayed 
	 **/
	private int casesPercent = 99;

	/**
	 * Indicates whether some goal types are not displayed
	 **/
	private boolean showGoalType = false;

	/**
	 * Arrays of goal type indicating for each one if it should be displayed
	 * or not. It is only valid when showGoalType is true.
	 **/
	private boolean[] showTypes = new boolean[GoalOrigin.getMaxGoalType()];

	{
		for (int i = 0; i < GoalOrigin.getMaxGoalType(); i++) {
			showTypes[i] = false;
		}

	}

	/**
	 * The list of available configurations
	 **/
	private TreeFilterConfiguration[] configurations;

	/**
	 * The button to select to display proved items
	 **/
	private Button proved;

	/**
	 * The button to select to display unproved items
	 **/
	private Button unProved;

	/**
	 * The text where proof percentage bound for a class is displayed
	 **/
	private Text classPercentMax;

	/**
	 * The text where proof percentage bound for a case is displayed
	 **/
	private Text methodPercentMax;

	/**
	 * The text where proof percentage bound for a class is displayed
	 **/
	private Text casesPercentMax;

	/**
	 * The button allowing to specify that only some goals type have to be 
	 * displayed
	 **/
	private Button goalType;

	/**
	 * The list of goal types
	 **/
	private List goalTypeList;

	/**
	 * The current viewer
	 */
	private ICaseExplorer viewer;

	/*@
	  @ private invariant configurations != null;
	  @*/

	/**
	 * Constructs the tree filter windows. Initializes the configurations.
	 * @param parent The parent shell
	 * @param v The current viewer
	 */
	public TreeFilterWindow(Shell parent, ICaseExplorer v) {
		super(parent);
		viewer = v;
		configurations = new TreeFilterConfiguration[3];
		configurations[0] = TreeFilterConfiguration.SHOW_UNPROVED;
		configurations[1] = TreeFilterConfiguration.SHOW_ALL;
		configurations[2] = TreeFilterConfiguration.SHOW_CASES;
	}

    /**
     * @return a grid data with the flag <code>grabExcessHorizontalSpace</code>
     * set
     */
	private static GridData gridData1() {
		GridData gd = new GridData();
		gd.grabExcessHorizontalSpace = true;
		return gd;
	}

    /**
     * Returns a grid data with a horizontal span.
     * @param horizontalSpan The horizontal span
     * @return a grid data with the flag <code>grabExcessHorizontalSpace</code>
     * set
     */
	private static GridData gridData2(int horizontalSpan) {
		GridData gd = new GridData();
		gd.grabExcessHorizontalSpace = true;
		gd.horizontalSpan = horizontalSpan;
		return gd;
	}

    /**
     * Creates a label
     * @param c The composite where the label is created
     * @param s The string of the label
     * @param gd The grid data of the label
     */
	private static void createLab(Composite c, String s, GridData gd) {
		Label res = new Label(c, SWT.HORIZONTAL);
		res.setText(s);
		res.setLayoutData(gd);
	}

	/**
	 * The dialog is displayed as follows :
	 * <pre>
	 * | Preset:      |<-                 combo box                          ->|
	 * | Show goals   | [] proved                                              |
	 * |              | [] unproved                                            |
	 * | Show classes | with proved percentage <= | []          | %            |
	 * | Show methods | with proved percentage <= | []          | %            |
	 * | Show cases   | with proved percentage <= | []          | %            |
	 * | [] Show goals of type                                                 |
	 * |<-                                  list                             ->|
	 * </pre>
	 */
	protected Control createDialogArea(Composite parent) {
		// set the title of the dialog
		parent.getShell().setText("LemmaViewer Filter");
		Composite c = new Composite(parent, SWT.NULL);
		GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 4;
		gridLayout.marginWidth = 5;
		c.setLayout(gridLayout);

		// add a choice for the different possible configurations
		Label configuration_label = new Label(c, SWT.HORIZONTAL);
		configuration_label.setText("Preset:");
		configuration_label.setLayoutData(gridData1());

		Combo combo = new Combo(c, SWT.READ_ONLY);
		combo.setLayoutData(gridData2(3));

		for (int i = 0; i < configurations.length; ++i) {
			combo.add(configurations[i].name);
		}
		// select the first item
		combo.select(0);

		combo.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				Combo combo = (Combo) e.widget;
				// combo.getText() provides the text of the selected element
				// combo.getSelectionIndex returns the index of the selected
				// item, or -1 of no item is selected (should never happen)
				int selected = combo.getSelectionIndex();
				if (selected != -1) {
					updateFromConfiguration(configurations[selected]);
				}
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		// original part of dialog
		createLab(c, "Show goals", gridData1());

		proved = new Button(c, SWT.CHECK);
		proved.setText("proved");
		proved.setSelection(showProved);
		proved.setLayoutData(gridData2(3));

		createLab(c, "", gridData1());
		unProved = new Button(c, SWT.CHECK);
		unProved.setText("unproved");
		unProved.setSelection(showUnProved);
		unProved.setLayoutData(gridData2(3));

		createLab(c, "Show classes", gridData1());
		createLab(c, "with proved percentage <=", gridData1());

		classPercentMax = new Text(c, SWT.SINGLE | SWT.BORDER);
		classPercentMax.setText("" + classPercent);
		classPercentMax.setLayoutData(gridData1());

		createLab(c, "%", gridData1());

		createLab(c, "Show methods", gridData1());
        createLab(c, "with proved percentage <=", gridData1());

		methodPercentMax = new Text(c, SWT.SINGLE | SWT.BORDER);
		methodPercentMax.setText("" + methodPercent);
		methodPercentMax.setLayoutData(gridData1());

        createLab(c, "%", gridData1());

        createLab(c, "Show cases", gridData1());
        createLab(c, "with proved percentage <=", gridData1());

		casesPercentMax = new Text(c, SWT.SINGLE | SWT.BORDER);
		casesPercentMax.setText("" + casesPercent);
		casesPercentMax.setLayoutData(gridData1());

        createLab(c, "%", gridData1());

		goalType = new Button(c, SWT.CHECK);
		goalType.setText("Show goals of type");
		goalType.setSelection(showGoalType);
		goalType.setLayoutData(gridData2(4));

		goalTypeList = new List(c, SWT.MULTI | SWT.BORDER);
		goalTypeList.setEnabled(showGoalType);
		for (byte i = 0; i < GoalOrigin.getMaxGoalType(); i++) {
			goalTypeList.add(GoalOrigin.getGoalTypeString(i, ""));
			if (showGoalType && showTypes[i])
				goalTypeList.select(i);
		}
		goalTypeList.setLayoutData(gridData2(4));

		goalType.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			public void widgetSelected(SelectionEvent e) {
				goalTypeList.setEnabled(!goalTypeList.isEnabled());
			}
		});

		return c;
	}

	/**
	 * Update the content of the window from the given configuration.
	 */
	/*@
	  @ requires conf != null;
	  @*/
	void updateFromConfiguration(TreeFilterConfiguration conf) {
		showProved = conf.showProved;
		showUnProved = conf.showUnProved;

		classPercent = conf.classPercent;
		methodPercent = conf.methodPercent;
		casesPercent = conf.casesPercent;
		showGoalType = conf.showGoalType;

		// copy the content of the showTypes array      
		System.arraycopy(conf.showTypes, 0, showTypes, 0, showTypes.length);

		// now, updates the interface content
		updateInterface();
	}

	/**
	 * Updates the current values from the content of the user interface.
	 */
	void updateFromInterface() {
		showProved = proved.getSelection();
		showUnProved = unProved.getSelection();
		try {
			classPercent = Integer.parseInt(classPercentMax.getText());
		} catch (NumberFormatException ne) {
			classPercent = 100;
		}
		try {
			methodPercent = Integer.parseInt(methodPercentMax.getText());
		} catch (NumberFormatException ne) {
			methodPercent = 100;
		}
		try {
			casesPercent = Integer.parseInt(casesPercentMax.getText());
		} catch (NumberFormatException ne) {
			casesPercent = 100;
		}
		showGoalType = goalType.getSelection();
		for (int i = 0; i < GoalOrigin.getMaxGoalType(); i++)
			showTypes[i] = goalTypeList.isSelected(i);

	}

	/**
	 * Updates the values displayed by the user interface from the values
	 * contained within the class.
	 */
	void updateInterface() {
		proved.setSelection(showProved);
		unProved.setSelection(showUnProved);
		classPercentMax.setText(Integer.toString(classPercent));
		methodPercentMax.setText(Integer.toString(methodPercent));
		casesPercentMax.setText(Integer.toString(casesPercent));
		goalType.setSelection(showGoalType);
		goalTypeList.setEnabled(showGoalType);
		for (byte i = 0; i < GoalOrigin.getMaxGoalType(); i++) {
			goalTypeList.add(GoalOrigin.getGoalTypeString(i, ""));
			if (showGoalType && showTypes[i])
				goalTypeList.select(i);
		}
	}

	/**
	 * Stores the content of the window into the given configuration.
	 */
	/*@
	  @ requires conf != null;
	  @*/
	void storeIntoConfiguration(TreeFilterConfiguration conf) {
		conf.showProved = showProved;
		conf.showUnProved = showUnProved;

		conf.classPercent = classPercent;
		conf.methodPercent = methodPercent;
		conf.casesPercent = casesPercent;
		conf.showGoalType = showGoalType;

		// copy the content of the showTypes array      
		System.arraycopy(showTypes, 0, conf.showTypes, 0, showTypes.length);

	}

	protected void okPressed() {
		updateFromInterface();

		viewer.displayStatus();
		setReturnCode(Window.OK);
		close();
	}
    
	/**
     * Returns the ipper proof percentage bound for a case to be displayed 
	 * @return <code>casesPercent</code>
	 */
	public int getCasesPercent() {
		return casesPercent;
	}

	/**
     * Returns the upper proof percentage bound for a class to be displayed 
	 * @return <code>classPercent</code>
	 */
	public int getClassPercent() {
		return classPercent;
	}

	/**
     * Returns the upper proof percentage bound for a method to be displayed.
	 * @return <code>methodPercent</code>
	 */
	public int getMethodPercent() {
		return methodPercent;
	}

	/**
     * Returns whether the proved item should be display or not.
	 * @return <code>showProved</code>
	 */
	public boolean isShowProved() {
		return showProved;
	}

	/**
     * Returns whether the unproved item should be display or not.
	 * @return <code>showUnProved</code>
	 */
	public boolean isShowUnProved() {
		return showUnProved;
	}

	/**
     * Returns whether some goal types are not displayed.
	 * @return <code>showGoalType</code>
	 */
	public boolean isShowGoalType() {
		return showGoalType;
	}

	/**
     * Returns whether a goal type should be displayed or not.
	 * @param i The goal type
	 */
	public boolean getShowTypes(int i) {
		return showTypes[i];
	}

}

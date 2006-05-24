//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackDefaultSpecEditor.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import java.util.Vector;

import jml2b.exceptions.Jml2bException;
import jml2b.structure.jml.Exsures;
import jml2b.structure.statement.Expression;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/**
 * Control allowing to edit the default values added when clauses are not 
 * specified.
 * 
 * @author A. Requet, L. Burdy
 */
public class JackDefaultSpecEditor {
	private Shell shell;

	private Button requiresTrue;
	private Button requiresOther;
	private Text requiresText;

	private Button ensuresOther;
	private Button ensuresTrue;
	private Text ensuresText;

	private Button modifiesNothing;
	private Button modifiesEverything;

	private JackProjectPropertyPage jppp;

	private static final String[] EXCEPTIONS =
		{
			"NullPointerException",
			"ClassCastException",
			"ArrayStoreException",
			"ArrayIndexOutOfBoundsException",
			"ArithmeticException" };

	private Button exsuresExceptionFalse;
	private Button exsuresExceptionTrue;
	private Button exsuresRuntimeException;
	private Button exsuresOther;
	private Text exsuresText;
	private Button[] exsuresButtons;

	public JackDefaultSpecEditor(Shell s, JackProjectPropertyPage jppp) {
		shell = s;
		this.jppp = jppp;
	}

	private static GridData getData(
		int width,
		int height,
		boolean expand_horizontal) {
		GridData data =
			new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL);

		data.grabExcessHorizontalSpace = expand_horizontal;
		data.grabExcessVerticalSpace = false;
		data.verticalAlignment = GridData.BEGINNING;
		data.horizontalSpan = width;
		data.verticalSpan = height;

		return data;
	}

	private static GridData getData(int width, int height) {
		GridData data =
			new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL);

		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = false;
		data.verticalAlignment = GridData.BEGINNING;
		data.horizontalSpan = width;
		data.verticalSpan = height;

		return data;
	}

	private Control createRequiresControl(Composite parent) {
		Group group = new Group(parent, SWT.SHADOW_NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);

		group.setText("requires");

		requiresTrue = new Button(group, SWT.RADIO);
		requiresTrue.setText("true");
		requiresTrue.setLayoutData(getData(2, 1));

		requiresOther = new Button(group, SWT.RADIO);
		requiresOther.setText("other");
		requiresOther.setLayoutData(getData(1, 1, false));

		requiresText = new Text(group, SWT.NONE | SWT.BORDER);

		requiresText.setLayoutData(getData(1, 1));

		SelectionListener s =
			new ActivateSelectionListener(requiresOther, requiresText, jppp);
		requiresOther.addSelectionListener(s);

		return group;
	}

	private Control createModifiesControls(Composite parent) {
		Group group = new Group(parent, SWT.SHADOW_NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);

		group.setText("modifies");

		modifiesEverything = new Button(group, SWT.RADIO);
		modifiesEverything.setText("\\everything");
		modifiesEverything.setLayoutData(getData(2, 1));
		modifiesEverything.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				jppp.setShouldGenerateImage(true);
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		modifiesNothing = new Button(group, SWT.RADIO);
		modifiesNothing.setText("\\nothing");
		modifiesNothing.setLayoutData(getData(2, 1));
		modifiesNothing.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				jppp.setShouldGenerateImage(true);
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		return group;
	}

	private Control createEnsuresControls(Composite parent) {
		Group group = new Group(parent, SWT.SHADOW_NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);

		group.setText("ensures");

		ensuresTrue = new Button(group, SWT.RADIO);
		ensuresTrue.setText("true");
		ensuresTrue.setLayoutData(getData(2, 1));

		ensuresOther = new Button(group, SWT.RADIO);
		ensuresOther.setText("other");
		ensuresOther.setLayoutData(getData(1, 1, false));

		ensuresText = new Text(group, SWT.BORDER);
		ensuresText.setLayoutData(getData(1, 1));

		ensuresTrue.setSelection(true);

		SelectionListener s =
			new ActivateSelectionListener(ensuresOther, ensuresText, jppp);
		ensuresOther.addSelectionListener(s);

		return group;
	}

	private Control createExsuresControls(Composite parent) {
		Group group = new Group(parent, SWT.SHADOW_NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);

		group.setText("exsures");

		exsuresExceptionFalse = new Button(group, SWT.RADIO | SWT.UP);
		exsuresExceptionFalse.setText("(Exception) false");
		exsuresExceptionFalse.setLayoutData(getData(2, 1));

		exsuresExceptionTrue = new Button(group, SWT.RADIO | SWT.UP);
		exsuresExceptionTrue.setText("(Exception) true");
		exsuresExceptionTrue.setLayoutData(getData(2, 1));

		exsuresRuntimeException = new Button(group, SWT.RADIO | SWT.UP);
		exsuresRuntimeException.setText("(RuntimeException) false :");
		exsuresRuntimeException.setLayoutData(getData(1, EXCEPTIONS.length));

		exsuresButtons = new Button[EXCEPTIONS.length];

		for (int i = 0; i < EXCEPTIONS.length; ++i) {
			Button tmp = new Button(group, SWT.CHECK);
			tmp.setText(EXCEPTIONS[i]);
			tmp.setLayoutData(getData(1, 1));

			exsuresButtons[i] = tmp;

		}

		exsuresOther = new Button(group, SWT.RADIO | SWT.UP);
		exsuresOther.setText("other");
		exsuresOther.setLayoutData(getData(1, 1));

		exsuresText = new Text(group, SWT.BORDER);
		exsuresText.setLayoutData(getData(1, 1));

		SelectionListener s =
			new ActivateSelectionListener(exsuresOther, exsuresText, jppp);
		exsuresOther.addSelectionListener(s);
		s =
			new ActivateSelectionArrayListener(
				exsuresRuntimeException,
				exsuresButtons,
				jppp);
		exsuresRuntimeException.addSelectionListener(s);

		return group;
	}

	public void createWidgets(Composite parent) {
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		parent.setLayout(layout);

		Control tmp;

		tmp = createRequiresControl(parent);
		tmp.setLayoutData(getData(1, 1));

		tmp = createModifiesControls(parent);
		tmp.setLayoutData(getData(1, 1));

		tmp = createEnsuresControls(parent);
		tmp.setLayoutData(getData(1, 1));

		tmp = createExsuresControls(parent);
		tmp.setLayoutData(getData(1, 1));
	}

	/**
	 * Sets all the fields to default values. 
	 */
	public void performDefaults() {
		ensuresTrue.setSelection(true);
		ensuresOther.setSelection(false);
		ensuresText.setEnabled(false);

		modifiesEverything.setSelection(true);
		modifiesNothing.setSelection(false);

		requiresTrue.setSelection(true);
		requiresOther.setSelection(false);
		requiresText.setEnabled(false);

		exsuresExceptionFalse.setSelection(true);
		exsuresExceptionTrue.setSelection(false);
		exsuresOther.setSelection(false);
		exsuresRuntimeException.setSelection(false);
		enableExceptions(false);
		exsuresText.setEnabled(false);
	}

	/**
	 * Updates the state of the controls depending on the state of the 
	 * given project.
	 * 
	 * @param project 
	 */
	public void updateControls(IProject project) {
		String tmp;

		// ensures		
		tmp = JackJml2bConfiguration.getDefaultJmlEnsuresText(project);
		ensuresText.setText(tmp != null ? tmp : "");

		if (JackJml2bConfiguration.isDefaultJmlEnsuresTrue(project)) {
			ensuresTrue.setSelection(true);
			ensuresOther.setSelection(false);
			ensuresText.setEnabled(false);
		} else {
			ensuresTrue.setSelection(false);
			ensuresOther.setSelection(true);
			ensuresText.setEnabled(true);
		}

		// requires
		tmp = JackJml2bConfiguration.getDefaultJmlRequiresText(project);
		requiresText.setText(tmp != null ? tmp : "");

		if (JackJml2bConfiguration.isDefaultJmlRequiresTrue(project)) {
			requiresTrue.setSelection(true);
			requiresOther.setSelection(false);
			requiresText.setEnabled(false);
		} else {
			requiresTrue.setSelection(false);
			requiresOther.setSelection(true);
			requiresText.setEnabled(true);
		}

		// modifies
		if (JackJml2bConfiguration
			.getDefaultJmlModifies(project)
			.equals(JackJml2bConfiguration.NOTHING)) {
			modifiesNothing.setSelection(true);
			modifiesEverything.setSelection(false);
		} else {
			modifiesEverything.setSelection(true);
			modifiesNothing.setSelection(false);
		}

		// exsures
		switch (JackJml2bConfiguration.getDefaultJmlExsuresType(project)) {
			case JackJml2bConfiguration.EXSURES_OTHER :
				exsuresOther.setSelection(true);
				exsuresText.setEnabled(true);
				enableExceptions(false);
				exsuresExceptionFalse.setSelection(false);
				exsuresExceptionTrue.setSelection(false);
				exsuresRuntimeException.setSelection(false);
				break;
			case JackJml2bConfiguration.EXSURES_EXCEPTION_FALSE :
				exsuresExceptionFalse.setSelection(true);
				exsuresExceptionTrue.setSelection(false);
				exsuresText.setEnabled(false);
				enableExceptions(false);
				exsuresOther.setSelection(false);
				exsuresRuntimeException.setSelection(false);
				break;
			case JackJml2bConfiguration.EXSURES_EXCEPTION_TRUE :
				exsuresExceptionFalse.setSelection(false);
				exsuresExceptionTrue.setSelection(true);
				exsuresText.setEnabled(false);
				enableExceptions(false);
				exsuresOther.setSelection(false);
				exsuresRuntimeException.setSelection(false);
				break;
			case JackJml2bConfiguration.EXSURES_RUNTIMEEXCEPTION_FALSE :
				exsuresRuntimeException.setSelection(true);
				exsuresText.setEnabled(false);
				enableExceptions(true);
				exsuresExceptionFalse.setSelection(false);
				exsuresExceptionTrue.setSelection(false);
				exsuresOther.setSelection(false);
				break;
		}

		String[] exceptions =
			JackJml2bConfiguration.getDefaultJmlExsuresExceptions(project);
		for (int i = 0; i < exsuresButtons.length; ++i) {
			exsuresButtons[i].setSelection(
				containsException(exceptions, exsuresButtons[i].getText()));
		}
		String str = JackJml2bConfiguration.getDefaultJmlExsuresOther(project);
		if (str != null) {
			exsuresText.setText(str);
		}
	}

	private static boolean containsException(String[] exceptions, String ex) {
		for (int i = 0; i < exceptions.length; ++i) {
			if (exceptions[i].indexOf(ex) != -1) {
				return true;
			}
		}
		return false;
	}

	private void enableExceptions(boolean enabled) {
		for (int i = 0; i < exsuresButtons.length; ++i) {
			exsuresButtons[i].setEnabled(enabled);
		}
	}

	/**
	 * Checks that the text fields contains parseable JML. Return 
	 * <code>true</code> if the fields are Ok, <code>false</code> 
	 * otherwise.
	 * 
	 * @param display_dialog indicates wether an error dialog should be 
	 *         displayed in case of error.  
	 * @return true if there is no problem within the field, false otherwise.
	 */
	public boolean checkFields(boolean display_dialog) {
		boolean ensures_ok = true;
		String problems = "";

		// checks ensures if it is selected
		if (ensuresOther.getSelection()) {
			try {
				// try to parse the content of the requires text field
				Expression.getFromString(ensuresText.getText());
			} catch (Jml2bException e) {
				ensures_ok = false;
				problems += "Ensures:\n" + e.getMessage();
			}
		}

		// checks requires
		boolean requires_ok = true;
		if (requiresOther.getSelection()) {
			try {
				Expression.getFromString(requiresText.getText());
			} catch (Jml2bException e) {
				requires_ok = false;
				problems += "Requires:\n" + e.getMessage();
			}
		}

		// checks exsures
		boolean exsures_ok = true;
		if (exsuresOther.getSelection()) {
			try {
				Exsures.getExsures(exsuresText.getText(), new Vector());
			} catch (Jml2bException e) {
				exsures_ok = false;
				problems += "Exsures:\n" + e.getMessage();
			}
		}

		boolean result = ensures_ok && requires_ok && exsures_ok;

		if (!result && display_dialog) {
			// display an error dialog
			MessageDialog.openError(shell, "Error in parameters", problems);
		}

		return result;
	}

	/**
	 * Updates the changes in the interface to the project properties.
	 */
	public boolean performOk(IProject project) {
		if (!checkFields(true)) {
			return false;
		}

		boolean changed = false;
		// requires
		changed
			|= JackJml2bConfiguration.setDefaultJmlRequiresTrue(
				project,
				requiresTrue.getSelection());
		changed
			|= JackJml2bConfiguration.setDefaultJmlRequiresText(
				project,
				requiresText.getText());

		// ensures
		changed
			|= JackJml2bConfiguration.setDefaultJmlEnsuresTrue(
				project,
				ensuresTrue.getSelection());
		changed
			|= JackJml2bConfiguration.setDefaultJmlEnsuresText(
				project,
				ensuresText.getText());

		// modifies
		changed
			|= JackJml2bConfiguration.setDefaultJmlModifies(
				project,
				modifiesNothing.getSelection()
					? JackJml2bConfiguration.NOTHING
					: JackJml2bConfiguration.EVERYTHING);

		//exsures
		// sets the selection type
		if (exsuresOther.getSelection()) {
			changed
				|= JackJml2bConfiguration.setDefaultJmlExsuresType(
					project,
					JackJml2bConfiguration.EXSURES_OTHER);
		} else if (exsuresRuntimeException.getSelection()) {
			changed
				|= JackJml2bConfiguration.setDefaultJmlExsuresType(
					project,
					JackJml2bConfiguration.EXSURES_RUNTIMEEXCEPTION_FALSE);
		} else if (exsuresExceptionTrue.getSelection()) {
			changed
				|= JackJml2bConfiguration.setDefaultJmlExsuresType(
					project,
					JackJml2bConfiguration.EXSURES_EXCEPTION_TRUE);
		} else {
			changed
				|= JackJml2bConfiguration.setDefaultJmlExsuresType(
					project,
					JackJml2bConfiguration.EXSURES_EXCEPTION_FALSE);
		}

		// stores the values
		changed
			|= JackJml2bConfiguration.setDefaultJmlExsuresExceptions(
				project,
				getSelectedExceptions());
		changed
			|= JackJml2bConfiguration.setDefaultJmlExsuresOther(
				project,
				exsuresText.getText());

		if (changed) {
			unsetJmlCompile(project);
		}
		return true;
	}

	void unsetJmlCompile(IContainer p) {
		try {
			IResource[] je = p.members();
			for (int i = 0; i < je.length; i++) {
				try {
					JackPlugin.unJmlCompile(je[i]);
				} catch (CoreException ce) {
				}
				if (je[i] instanceof IContainer)
					unsetJmlCompile((IContainer) je[i]);
			}
		} catch (CoreException jme) {
		}
	}

	private String[] getSelectedExceptions() {
		int count = 0;
		for (int i = 0; i < exsuresButtons.length; ++i) {
			if (exsuresButtons[i].getSelection()) {
				++count;
			}
		}
		String[] result = new String[count];
		int current = 0;
		for (int i = 0; i < exsuresButtons.length; ++i) {
			if (exsuresButtons[i].getSelection()) {
				result[current++] = "java.lang." + exsuresButtons[i].getText();
			}
		}
		return result;
	}
}

/**
 * Class that allows activating and deactivating a control when the corresponding 
 * button is selected or deselected.
 * 
 * @author A. Requet
 */
class ActivateSelectionListener implements SelectionListener {
	private Control control;
	private Button button;
	private JackProjectPropertyPage jppp;


	public ActivateSelectionListener(Button b, Control c, JackProjectPropertyPage jppp) {
		control = c;
		button = b;
		this.jppp= jppp;
	}

	public void widgetDefaultSelected(SelectionEvent e) {
	}

	public void widgetSelected(SelectionEvent e) {
		control.setEnabled(button.getSelection());
		jppp.setShouldGenerateImage(true);
	}
}

/**
 * Class that allows activating and deactivating an array of controls when the 
 * corresponding button is selected or deselected.
 * 
 * @author A. Requet
 */
class ActivateSelectionArrayListener implements SelectionListener {
	private Control[] controls;
	private Button button;
	private JackProjectPropertyPage jppp;

	public ActivateSelectionArrayListener(Button b, Control[] c, JackProjectPropertyPage jppp) {
		controls = c;
		button = b;
		this.jppp= jppp;
	}

	public void widgetDefaultSelected(SelectionEvent e) {
	}

	public void widgetSelected(SelectionEvent e) {
		boolean enabled = button.getSelection();
		for (int i = 0; i < controls.length; ++i) {
			controls[i].setEnabled(enabled);
		}
		jppp.setShouldGenerateImage(true);
	}
}
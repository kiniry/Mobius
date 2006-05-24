//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.metrics;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;

/**
 * Filter dialog for the metrics view.
 * 
 * @author L. Burdy
 */
public class MetricsFilterWindow extends Dialog {

	static final int PROJECT = 0;
	static final int PACKAGE = 1;
	static final int RESSOURCE_ONLY = 2;

	private int filterType;

	private Button project;
	private Button package_;
	private Button ressource;
	
	private MetricsView mw;

	MetricsFilterWindow(Shell parent, MetricsView mw) {
		super(parent);
		this.mw = mw;
		filterType = PACKAGE;
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

	protected Control createDialogArea(Composite parent) {
		parent.getShell().setText("Metrics Filter");
		Composite c = new Composite(parent, SWT.NULL);
		GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		gridLayout.marginWidth = 5;
		c.setLayout(gridLayout);

		Group group = new Group(c, SWT.SHADOW_NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);

		group.setText("Show");

		project = new Button(group, SWT.RADIO);
		project.setText(" All the files of the same project");
		project.setLayoutData(getData(2, 1));
		if (filterType == PROJECT)
			project.setSelection(true);

		package_ = new Button(group, SWT.RADIO);
		package_.setText(" All the files of the same package");
		package_.setLayoutData(getData(2, 1));
		if (filterType == PACKAGE)
			package_.setSelection(true);

		ressource = new Button(group, SWT.RADIO);
		ressource.setText(" Only the selected file");
		ressource.setLayoutData(getData(2, 1));
		if (filterType == RESSOURCE_ONLY)
			ressource.setSelection(true);
		return c;
	}

	protected void okPressed() {
		if (project.getSelection())
			filterType = PROJECT;
		else if (package_.getSelection())
			filterType = PACKAGE;
		else
			filterType = RESSOURCE_ONLY;
		mw.refresh();
		close();
	}

	/**
	 * @return
	 */
	public int getFilterType() {
		return filterType;
	}

}

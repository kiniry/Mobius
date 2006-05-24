//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import jack.plugin.JackJml2bConfiguration;
import jpov.Icons;
import jpov.structure.Goal;
import jpov.structure.LemmaHierarchy;
import jpov.viewer.lemma.LemmaView;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.part.ViewPart;

/**
 * View displaying a lemma.
 * 
 * @author L. Burdy
 **/
public class LemmaViewer extends ViewPart implements ILemmaViewer {

	LemmaView lemmaView;
	HorizontalAction horizontalAction;
	VerticalAction verticalAction;
	ApplySubstitutionAction applySubstitutionAction;
	NonApplySubstitutionAction nonApplySubstitutionAction;

	public void createPartControl(Composite parent) {
		MenuManager mm =
			(MenuManager) getViewSite().getActionBars().getMenuManager();
		MenuManager smm = new MenuManager("Splitting views");

		horizontalAction = new HorizontalAction(this);
		horizontalAction.setChecked(true);
		verticalAction = new VerticalAction(this);
		smm.add(horizontalAction);
		smm.add(verticalAction);
		mm.add(new Separator());
		mm.add(smm);
		smm = new MenuManager("Java view");

		applySubstitutionAction = new ApplySubstitutionAction(this);
		applySubstitutionAction.setChecked(true);
		nonApplySubstitutionAction = new NonApplySubstitutionAction(this);
		smm.add(applySubstitutionAction);
		smm.add(nonApplySubstitutionAction);
		mm.add(smm);

		lemmaView =
			new LemmaView(
				new JackJml2bConfiguration((IProject) null, null),
				parent,
				horizontalAction.isChecked());
		getViewSite().getActionBars().getToolBarManager().add(
			new FilterAction(lemmaView));
		getViewSite().getActionBars().updateActionBars();
		TableCopyAction copyAction = new TableCopyAction(lemmaView);
		getViewSite().getActionBars().setGlobalActionHandler(
			ActionFactory.COPY.getId(),
			copyAction);

	}

	void redraw() {
		lemmaView.redraw(
			new JackJml2bConfiguration((IProject) null, null),
			horizontalAction.isChecked(),
			applySubstitutionAction.isChecked());

	}

	/**
	 * Sets the goal to be displayed in the lemma views
	 * @param g The goal to display
	 **/
	public void setGoalText(Goal g) {
		if (g != null)
			setPartName(g.getOriginString());
		else
			setPartName("Lemma Viewer");
		lemmaView.setGoalText(g, applySubstitutionAction.isChecked());
	}

	/**
	 * Sets the lemma to be displayed in the lemma views
	 * @param l The lemma from whitch hypotheses have to be displayed
	 **/
	public void setHypText(jpov.structure.Lemma l) {
		lemmaView.setHypText(l);
	}

	public void setHypText(LemmaHierarchy l) {
		lemmaView.setHypText(l);
	}

	public void setFocus() {
	}

}

/**
 * This action allows to open the filter dialog.
 *
 *  @author L. Burdy
 **/
class FilterAction extends Action {

	LemmaView lemmaView;

	FilterAction(LemmaView lemmaView) {
		setText("Checked");
		setImageDescriptor(Icons.FILTER_DESCRIPTOR);

		this.lemmaView = lemmaView;
	}

	public void run() {
		lemmaView.getLemmaFilterWindow().open();
	}
}

/**
 * This action allows to copy an hypothesis.
 *
 *  @author L. Burdy
 **/
class TableCopyAction extends Action {

	LemmaView l;

	TableCopyAction(LemmaView lv) {
		l = lv;
	}

	public void run() {
		TableViewer tv = l.getSelectedTable();
		if (tv != null) {
			String s =
				tv
					.getTable()
					.getItem(tv.getTable().getSelectionIndex())
					.getText();
			Text t = new Text(tv.getTable(), SWT.NONE);
			t.setText(s);
			t.setSelection(0, s.length());
			t.copy();

		}
	}
}

/**
 * This action allows to set the application of the substitutions to goal.
 *
 *  @author L. Burdy
 *
 */
class ApplySubstitutionAction extends Action {

	LemmaViewer t;

	ApplySubstitutionAction(LemmaViewer t) {
		super("Apply substitutions", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.redraw();
	}
}

/**
 * This action allows to display goal without applying substitutions.
 *
 *  @author L. Burdy
 **/
class NonApplySubstitutionAction extends Action {

	LemmaViewer t;

	NonApplySubstitutionAction(LemmaViewer t) {
		super("Do not apply substitutions", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.redraw();
	}
}

/**
 * This action allows to display subwindows horizontally.
 *
 *  @author L. Burdy
 **/
class HorizontalAction extends Action {

	LemmaViewer t;

	HorizontalAction(LemmaViewer t) {
		super("Horizontal", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.redraw();
	}
}

/**
 * This action allows to display subwindows vertically.
 *
 *  @author L. Burdy
 **/
class VerticalAction extends Action {

	LemmaViewer t;

	VerticalAction(LemmaViewer t) {
		super("Vertical", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.redraw();
	}
}

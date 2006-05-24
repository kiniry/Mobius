//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: GoalContentProvider
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import jml2b.languages.ILanguage;
import jpov.structure.Goal;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * Class that give the content to display in the goal folder of the lemma view.
 * @author A. Requet, L. Burdy
 **/
public final class GoalContentProvider implements IStructuredContentProvider {

	/**
	 * The language in witch this goal content provider displays a goal.
	 **/
	ILanguage language;
	
	boolean applySubstitution;

	/**
	 * Constructs a new goal content provider.
	 * @param il The language
	 **/
	GoalContentProvider(ILanguage il) {
		language = il;
	}

	/**
	 * If the <code>inputElement</code> is a goal, returns an array containing
	 * as first element the goal and as remaining elements each lines of the 
	 * string resulting from the translatation of the goal.
	 * @param inputElement
	 * @return the lines to display 
	 **/
	public Object[] getElements(Object inputElement) {
		if (inputElement instanceof Goal)
			return jml2b.util.Util.tokenize(
				language.displayGoal((Goal) inputElement, applySubstitution),
				"\n");
		else
			return new Object[0];
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

	public void dispose() {
	}
	/**
	 * @param b
	 */
	public void setApplySubstitution(boolean b) {
		applySubstitution = b;
	}

}

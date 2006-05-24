//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: MyLabelProvider.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.VirtualFormula;
import jpov.Icons;
import jpov.structure.Goal;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

/**
 * This class implements a label provider for hypothesis and goal.
 * @author L. Burdy
 **/
public class MyLabelProvider extends LabelProvider {

	/**
	 * Returns the text associated with an hypothese line or with the goal.
	 **/
	public String getText(Object element) {
		if (element instanceof HypLine)
			return ((HypLine) element).getText();
		else if (element instanceof Goal)
			return ((Goal) element).getOriginString();
		else
			return (String) element;
	}

	/**
	 * Returns the image to display if the element corresponds to the first 
	 * line of an hypothese or to a goal. The displayed image depends on the
	 * origin of the element.
	 **/
	public Image getImage(Object element) {
		if (element instanceof HypLine) {
			HypLine hl = (HypLine) element;
			if (hl.isFirst()) {
				switch (hl.getOrigin()) {
					case jml2b
						.pog
						.lemma
						.VirtualFormula
						.STATIC_FINAL_FIELDS_INVARIANT :
					case jml2b.pog.lemma.VirtualFormula.INVARIANT :
						return Icons.INVARIANT;
					case jml2b.pog.lemma.VirtualFormula.LOCALES :
						return Icons.LOCALES;
					case jml2b.pog.lemma.VirtualFormula.ENSURES :
						return Icons.ENSURES;
					case jml2b.pog.lemma.VirtualFormula.EXSURES :
						return Icons.EXSURES;
					case jml2b.pog.lemma.VirtualFormula.REQUIRES :
						return Icons.REQUIRES;
					case jml2b.pog.lemma.VirtualFormula.LOOP_INVARIANT :
						return Icons.LOOP_INVARIANT;
					case jml2b.pog.lemma.VirtualFormula.LOOP_EXSURES :
						return Icons.LOOP_EXSURES;
					case jml2b.pog.lemma.VirtualFormula.BLOCK_ENSURES :
						return Icons.ENSURES;
					case jml2b.pog.lemma.VirtualFormula.BLOCK_EXSURES :
						return Icons.EXSURES;
						case VirtualFormula.ASSERT :
						return Icons.ASSERT;
					default :
						return null;
				}
			} else
				return null;
		} else if (element instanceof Goal)
			switch (((Goal) element).getGoalType()) {
				case GoalOrigin.MEMBER_INVARIANT :
				case GoalOrigin.STATIC_INVARIANT :
					return Icons.INVARIANT;
				default :
					return null;
			} else
			return null;
	}

	public void dispose() {
	}
}

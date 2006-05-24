//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeLabelProvider.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jack.plugin.perspective.ICaseExplorer;
import jpov.Icons;
import jpov.structure.TreeObject;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

/**
 * This class provides methods that associate an image and a text to a node 
 * of the tree in the viewer.
 * @author L. Burdy
 **/
public class TreeLabelProvider extends LabelProvider {

	ICaseExplorer caseExp;

	public TreeLabelProvider(ICaseExplorer ice) {
		caseExp = ice;
	}

	/**
	 * Returns the image associated with the node depending of the proof 
	 * rate and the fact that it is checked or not.
	 * @return The image displayed in the tree.        
	 **/
	public Image getImage(Object element) {
		if (element instanceof TreeObject) {
			TreeObject t = (TreeObject) element;
			if (t.isChecked()) {
				return Icons.CHECKED;
			}
			if (t.isProved()) {
				return Icons.PROVED;
			}
			if (t.getNbPoProved() == 0) {
				return Icons.UNPROVED;
			}
			return Icons.provedImages[t.percentProved()
				* Icons.PROVED_IMAGES_COUNT
				/ 100];
		} else {
			return null;
		}
	}

	/**
	 * Returns the text associated with the node.
	 * @return the node text.
	 **/
	public String getText(Object element) {
		if (element instanceof TreeObject)
			return ((TreeObject) element).getText(caseExp.getLayout());
		else
			return "";
	}

	/**
	 * Performs no action
	 **/
	public void dispose() {}
}

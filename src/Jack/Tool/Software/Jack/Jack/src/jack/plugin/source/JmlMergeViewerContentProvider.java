//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import jml2b.util.JmlFileStream;
import jml2b.util.UpdatedJmlFile;

import org.eclipse.compare.contentmergeviewer.IMergeViewerContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;

/**
 * Content provider for the JML merge viewer.
 * 
 * @author L. Burdy
 **/
public 	class JmlMergeViewerContentProvider implements IMergeViewerContentProvider {

	public Object getAncestorContent(Object input) {
		return null;
	}

	public Image getAncestorImage(Object input) {
		return null;
	}

	public String getAncestorLabel(Object input) {
		return null;
	}

	public Object getLeftContent(Object input) {
		if (input != null)
			return new JmlFileStream(((UpdatedJmlFile) input).getJf());
		else
			return null;
	}

	public Image getLeftImage(Object input) {
		return null;
	}

	public String getLeftLabel(Object input) {
		if (input != null)
			return ((UpdatedJmlFile) input).getJf().getName();
		else
			return null;
	}

	public Object getRightContent(Object input) {
		if (input != null)
			if (((UpdatedJmlFile) input).getNewF() != null)
				return new JmlFileStream(
					((UpdatedJmlFile) input).getNewF());
			else
				return new JmlFileStream(((UpdatedJmlFile) input).getJf());
		else
			return null;
	}

	public Image getRightImage(Object input) {
		return null;
	}

	public String getRightLabel(Object input) {
		if (input != null)
			return "Updated " + ((UpdatedJmlFile) input).getJf().getName();
		else
			return null;
	}

	public boolean isLeftEditable(Object input) {
		return false;
	}

	public boolean isRightEditable(Object input) {
		return false;
	}

	public void saveLeftContent(Object input, byte[] bytes) {
	}

	public void saveRightContent(Object input, byte[] bytes) {
	}
	public boolean showAncestor(Object input) {
		return false;
	}

	public void dispose() {
	}

	public void inputChanged(
		Viewer viewer,
		Object oldInput,
		Object newInput) {
	}

}


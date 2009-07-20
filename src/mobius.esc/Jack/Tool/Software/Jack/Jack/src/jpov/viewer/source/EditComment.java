//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: EditComment
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.source;

import java.util.Enumeration;
import java.util.Vector;

import jpov.viewer.JpovViewer;
import jpov.viewer.tree.TreeItemSelection;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseTrackListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Label;

/**
 * This class implements a mouse track listener that displays a label in the
 * source text when the mouse stand over a highlighted box that contains 
 * informations to display.
 * @author L. Burdy
 */
public class EditComment implements MouseTrackListener {

	/**
	 * The yellow color in which the label is displayed.
	 **/
	private static org.eclipse.swt.graphics.Color YELLOW =
		new org.eclipse.swt.graphics.Color(
			JpovViewer.getDisplay(),
			200,
			200,
			10);

	/**
	 * The font in which the label is displayed.
	 **/
	private static Font f = new Font(JpovViewer.getDisplay(), "Tahoma", 14, 0);

	/**
	 * The set of labels org.eclipse.swt.widgets.Label
	 **/
	private Vector lab = new Vector();

	/**
	 * The current viewer
	 **/
	private SourceView ew;

	/**
	 * The current selection listener of the tree 
	 **/
	private TreeItemSelection ehl;

	/**
	 * Constructs a listener
	 * @param ew The current viewer
	 * @param ehl The current node selection listener of the tree
	 **/
	public EditComment(SourceView ew, TreeItemSelection ehl) {
		this.ew = ew;
		this.ehl = ehl;
	}

	/**
	 * Performs no action
	 **/
	public void mouseEnter(org.eclipse.swt.events.MouseEvent e) {
	}

	/**
	 * Disposes the label
	 **/
	public void mouseExit(org.eclipse.swt.events.MouseEvent ev) {
		Enumeration e = lab.elements();
		while (e.hasMoreElements()) {
			Label element = (Label) e.nextElement();
			element.dispose();
		}
	}

	/**
	 * Creates a label and displays it if the mouse points to an highlighted box.
	 * @param e The mouse event
	 **/
	public void mouseHover(org.eclipse.swt.events.MouseEvent ev) {
		Enumeration e = lab.elements();
		while (e.hasMoreElements()) {
			Label element = (Label) e.nextElement();
			element.dispose();
		}

		// loop on the current labels set    
		Enumeration en = ehl.getLabels();
		while (en.hasMoreElements()) {
			Box b = (Box) en.nextElement();
			if (b.includes(ew.getSourceText(), ev.x, ev.y)) {
				// The mouse position is included in the box
				Label labl =
					new org.eclipse.swt.widgets.Label(
						(org.eclipse.swt.widgets.Composite) ev.getSource(),
						SWT.HORIZONTAL);
				labl.setFont(f);
				labl.setBackground(YELLOW);
				labl.setText(b.getCommentText());
				Point p = labl.computeSize(SWT.DEFAULT, SWT.DEFAULT);
				labl.setBounds(
					b.getX(ew.getSourceText()),
					b.getY(ew.getSourceText()) - p.y,
					p.x,
					p.y);
				lab.add(labl);
			}
		}
	}

}

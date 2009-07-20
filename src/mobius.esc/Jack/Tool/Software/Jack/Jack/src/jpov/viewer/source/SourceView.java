//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Source.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.source;

import jack.util.Logger;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

import jpov.JpoFile;
import jpov.viewer.JpovViewer;
import jpov.viewer.tree.TreeView;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;

/**
 * This class implements the part of view that contains the source code.
 * @author burdy
 */
public class SourceView {

	/**
	 * The label containing the name of the edited file.
	 */
	private Label source_folder;

	/**
	 * The source text
	 */
	private StyledText sourceText;

	/**
	 * The contextual menu of the source text
	 */
	private Menu stMenu;

	/**
	 * The selection listener for the contextual menu
	 */
	private SelectionListener stSelectionListener;

	/**
	 * The mouse listener of the source text
	 */
	private MouseListener stMouseListener;

	/**
	 * Constructs the view containing the source.
	 * @param right_sform The form containg the view
	 * @param pov The currently edited jpo file
	 * @param leftTree The associated tree
	 * @param viewer The current viewer
	 * @param ab The current Atelier B server
	 * @param f The font in witch the text should be displayed
	 */
	public SourceView(
		SashForm right_sform,
		JpoFile pov,
		TreeView leftTree,
		JpovViewer viewer,
		FontData f) {

		Font styledTextFont = new Font(JpovViewer.getDisplay(), f);

		ViewForm source_pane = new ViewForm(right_sform, SWT.NONE);

		source_folder = new Label(source_pane, SWT.NONE);
		if (pov != null && pov.getJmlFile() != null)
			source_folder.setText(pov.getJmlFile().getFileName().getName());
		source_pane.setTopLeft(source_folder);

		ScrolledComposite compose =
			new ScrolledComposite(
				source_pane,
				SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER);

		source_pane.setContent(compose);

		compose.getVerticalBar().setIncrement(5);

		sourceText = new StyledText(compose, SWT.NULL);
		sourceText.setFont(styledTextFont);

		// add sourceText to compose here so that the updateTextSize method
		// can be used. 
		compose.setContent(sourceText);
		if (pov != null && pov.getJmlFile() != null) {
			loadFile(pov.getJmlFile().getFileName());
			updateTextSize();
		}

		// add the mouse track listener to display comment
		sourceText.addMouseTrackListener(
			new EditComment(this, leftTree.getEhl()));

		// add the menu
		stMenu = new Menu(sourceText);
		MenuItem mi = new MenuItem(stMenu, SWT.FLAT);
		mi.setText("Wrong path");

		if (pov != null) {
			mi.addSelectionListener(stSelectionListener);
			stMouseListener = new SourceTextMenu(viewer, stMenu);
			sourceText.addMouseListener(stMouseListener);
		}

	}

	/**
	 * Update the displayed text from a loaded file
	 * @param f The loaded file
	 **/
	private void loadFile(File f) {
		try {
			Reader in = new FileReader(f);
			char[] buff = new char[4096];
			int nch;
			while ((nch = in.read(buff, 0, buff.length)) != -1) {
				sourceText.append(new String(buff, 0, nch));
			}
		} catch (IOException e) {
			Logger.err.println(e.toString());
		}
	}

	/** 
	 * Update the size of the text control according to the size of the 
	 * text it contains.
	 */
	private void updateTextSize() {
		if (sourceText == null) {
			return;
		}
		// get the scrolledcomposite widget.
		ScrolledComposite compose = (ScrolledComposite) sourceText.getParent();

		int maxColumn = 0, j;

		for (int i = 0; i < sourceText.getLineCount() - 1; i++)
			if (maxColumn
				< (j =
					sourceText.getOffsetAtLine(i + 1)
						- sourceText.getOffsetAtLine(i)))
				maxColumn = j;

		// setting minimal width and height should work better than setting the
		// size for sources that uses less than 80 columns.
		compose.setMinWidth(maxColumn * 8);
		compose.setMinHeight(
			sourceText.getLineCount() * (sourceText.getLineHeight() + 1));

		compose.setExpandHorizontal(true);
		compose.setExpandVertical(true);
	}

	/**
	 * Updates the content of the view
	 * @param pov The currently viewed jpo file
	 * @param viewer The current viewer
	 * @param ab The current Atelier B Server
	 */
	public void updateContent(JpoFile pov, JpovViewer viewer) {
		source_folder.setText(pov.getJmlFile().getFileName().getName());
		sourceText.setText("");
		loadFile(pov.getJmlFile().getFileName());

		// Remove the current selcetion listener and add a new one
		if (stSelectionListener != null)
			stMenu.getItem(0).removeSelectionListener(stSelectionListener);
//		stSelectionListener = new SourceTextMenuListener(pov, viewer, ab);
		stMenu.getItem(0).addSelectionListener(stSelectionListener);

		// Remove the current mouse listener and add a new one
		if (stMouseListener != null)
			sourceText.removeMouseListener(stMouseListener);
		stMouseListener = new SourceTextMenu(viewer, stMenu);
		sourceText.addMouseListener(stMouseListener);
		updateTextSize();
	}

	/**
	 * Clear the view
	 */
	public void erase() {
		sourceText.setText("");
		source_folder.setText("");
	}

	/**
	 * Returns the source text.
	 * @return <code>sourceText</code>
	 */
	public StyledText getSourceText() {
		return sourceText;
	}

}

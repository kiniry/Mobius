//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jack.plugin.edit;

import jack.plugin.JackPlugin;

import java.io.IOException;
import java.io.StringReader;
import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.LineStyleEvent;
import org.eclipse.swt.custom.LineStyleListener;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;

/**
 * Line styler for JML files.
 *
 *  @author L. Burdy
 **/
public class JavaLineStyler implements LineStyleListener {

	public static final int EOF = -1;
	public static final int EOL = 10;

	public static final int WORD = 0;
	public static final int WHITE = 1;
	public static final int KEY = 2;
	public static final int MULTI_COMMENT = 3;
	public static final int STRING = 5;
	public static final int OTHER = 6;
	public static final int NUMBER = 7;
	public static final int MULTI_COMMENT_JML = 8;
	public static final int KEY_JML = 9;
	public static final int SINGLE_COMMENT = 10;
	public static final int SINGLE_COMMENT_JML = 11;

	public static final int MAXIMUM_TOKEN = 12;

	private JavaScanner scanner;

	private Color[] tokenColors;

	private Color[] colors;

	private Vector blockComments = new Vector();

	private Vector blockCommentsJmlMultiLine = new Vector();

	private Vector blockCommentsJmlSingleLine = new Vector();

	private Vector boxes;

	public void setScanner(JavaScanner scanner) {
		this.scanner = scanner;
	}
	
	public JavaLineStyler(JavaScanner scan) {
		initializeColors();
		boxes = new Vector();
		scanner = scan;
	}

	Color getColor(int type) {
		if (type < 0 || type >= tokenColors.length) {
			return null;
		}
		return tokenColors[type];
	}

	boolean inBlockComment(Vector block, int start, int end) {
		for (int i = 0; i < block.size(); i++) {
			int[] offsets = (int[]) block.elementAt(i);
			// start of comment in the line
			if ((offsets[0] >= start) && (offsets[0] <= end))
				return true;
			// end of comment in the line
			if ((offsets[1] >= start) && (offsets[1] <= end))
				return true;
			if ((offsets[0] <= start) && (offsets[1] >= end))
				return true;
		}
		return false;
	}

	boolean inBlock(Vector block, int o) {
		for (int i = 0; i < block.size(); i++) {
			int[] offsets = (int[]) block.elementAt(i);
			// start of comment in the line
			if (offsets[0] <= o && o <= offsets[1])
				return true;
		}
		return false;
	}

	void initializeColors() {
		IPreferenceStore javaPrefs = PreferenceConstants.getPreferenceStore();
		Display display = Display.getDefault();
		colors = new Color[] { new Color(display, new RGB(0, 0, 0))};
		tokenColors = new Color[MAXIMUM_TOKEN];
		tokenColors[WORD] = colors[0];
		tokenColors[WHITE] = colors[0];
		tokenColors[KEY] =
			new Color(
				display,
				PreferenceConverter.getColor(
					javaPrefs,
					PreferenceConstants.EDITOR_JAVA_KEYWORD_COLOR));

		tokenColors[MULTI_COMMENT] =
			new Color(
				display,
				PreferenceConverter.getColor(
					javaPrefs,
					PreferenceConstants.EDITOR_MULTI_LINE_COMMENT_COLOR));
		tokenColors[STRING] =
			new Color(
				display,
				PreferenceConverter.getColor(
					javaPrefs,
					PreferenceConstants.EDITOR_STRING_COLOR));
		tokenColors[OTHER] = colors[0];
		tokenColors[NUMBER] = colors[0];
		tokenColors[MULTI_COMMENT_JML] =
			new Color(display, JackPlugin.getMultiCommentJmlColor());
		tokenColors[KEY_JML] =
			new Color(display, JackPlugin.getJmlKeywordColor());
		tokenColors[SINGLE_COMMENT] =
			new Color(
				display,
				PreferenceConverter.getColor(
					javaPrefs,
					PreferenceConstants.EDITOR_SINGLE_LINE_COMMENT_COLOR));
		tokenColors[SINGLE_COMMENT_JML] =
			new Color(display, JackPlugin.getSingleCommentJmlColor());
	}

	void disposeColors() {
		for (int i = 0; i < colors.length; i++) {
			colors[i].dispose();
		}
	}

	public void clearBoxes() {
		boxes = new Vector();
	}

	public void addBox(Color fgc, Color bgc, int offset, int length) {
		boxes.add(new Box(fgc, bgc, offset, length));
	}

	Box inBox(int offset) {
		Enumeration e = boxes.elements();
		while (e.hasMoreElements()) {
			Box element = (Box) e.nextElement();
			if (element.in(offset))
				return element;
		}
		return null;
	}

	/**
	 * Event.detail			line start offset (input)	
	 * Event.text 			line text (input)
	 * LineStyleEvent.styles 	Enumeration of StyleRanges, need to be in order. (output)
	 * LineStyleEvent.background 	line background color (output)
	 */
	public void lineGetStyle(LineStyleEvent event) {
		Vector styles = new Vector();
		int token;
		StyleRange lastStyle;
		Color defaultFgColor = ((Control) event.widget).getForeground();
		Color color;
		Box box;
		scanner.setRange(event.lineText);
		token = scanner.nextToken();
		while (token != EOF) {
			if (inBlock(blockComments,
				scanner.getStartOffset() + event.lineOffset)) {
				StyleRange style =
					new StyleRange(
						scanner.getStartOffset() + event.lineOffset,
						scanner.getLength(),
						getColor(MULTI_COMMENT),
						null);
				if (styles.isEmpty()) {
					styles.addElement(style);
				} else {
					// Merge similar styles.  Doing so will improve performance.
					lastStyle = (StyleRange) styles.lastElement();
					if (lastStyle.similarTo(style)
						&& (lastStyle.start + lastStyle.length == style.start)) {
						lastStyle.length += style.length;
					} else {
						styles.addElement(style);
					}
				}
			} else if (
				(box = inBox(scanner.getStartOffset() + event.lineOffset))
					!= null) {
				StyleRange style =
					new StyleRange(
						scanner.getStartOffset() + event.lineOffset,
						scanner.getLength(),
						box.getFgcolor(),
						box.getBgcolor());
				if (token == KEY) {
					style.fontStyle = SWT.BOLD;
				}
				if (styles.isEmpty()) {
					styles.addElement(style);
				} else {
					// Merge similar styles.  Doing so will improve performance.
					lastStyle = (StyleRange) styles.lastElement();
					if (lastStyle.similarTo(style)
						&& (lastStyle.start + lastStyle.length == style.start)) {
						lastStyle.length += style.length;
					} else {
						styles.addElement(style);
					}
				}
			} else if (
				inBlock(
					blockCommentsJmlMultiLine,
					scanner.getStartOffset() + event.lineOffset)) {
				if (token != KEY_JML)
					token = MULTI_COMMENT_JML;
				StyleRange style =
					new StyleRange(
						scanner.getStartOffset() + event.lineOffset,
						scanner.getLength(),
						getColor(token),
						null);
				if (token == KEY_JML) {
					style.fontStyle = SWT.BOLD;
				}
				if (styles.isEmpty()) {
					styles.addElement(style);
				} else {
					// Merge similar styles.  Doing so will improve performance.
					lastStyle = (StyleRange) styles.lastElement();
					if (lastStyle.similarTo(style)
						&& (lastStyle.start + lastStyle.length == style.start)) {
						lastStyle.length += style.length;
					} else {
						styles.addElement(style);
					}
				}
			} else if (
				inBlock(
					blockCommentsJmlSingleLine,
					scanner.getStartOffset() + event.lineOffset)) {
				if (token != KEY_JML)
					token = SINGLE_COMMENT_JML;
				StyleRange style =
					new StyleRange(
						scanner.getStartOffset() + event.lineOffset,
						scanner.getLength(),
						getColor(token),
						null);
				if (token == KEY_JML) {
					style.fontStyle = SWT.BOLD;
				}
				if (styles.isEmpty()) {
					styles.addElement(style);
				} else {
					// Merge similar styles.  Doing so will improve performance.
					lastStyle = (StyleRange) styles.lastElement();
					if (lastStyle.similarTo(style)
						&& (lastStyle.start + lastStyle.length == style.start)) {
						lastStyle.length += style.length;
					} else {
						styles.addElement(style);
					}
				}
			} else if (token == OTHER) {
				// do nothing for non-colored tokens
			} else if (token != WHITE) {
				if (token == KEY_JML)
					token = WORD;
				color = getColor(token);
				// Only create a style if the token color is different than the 
				// widget's default foreground color and the token's style is not 
				// bold.  Keywords are bolded.
				if ((!color.equals(defaultFgColor)) || (token == KEY)) {
					StyleRange style =
						new StyleRange(
							scanner.getStartOffset() + event.lineOffset,
							scanner.getLength(),
							color,
							null);
					if (token == KEY) {
						style.fontStyle = SWT.BOLD;
					}
					if (styles.isEmpty()) {
						styles.addElement(style);
					} else {
						// Merge similar styles.  Doing so will improve performance.
						lastStyle = (StyleRange) styles.lastElement();
						if (lastStyle.similarTo(style)
							&& (lastStyle.start + lastStyle.length
								== style.start)) {
							lastStyle.length += style.length;
						} else {
							styles.addElement(style);
						}
					}
				}
			} else if (
				(!styles.isEmpty())
					&& ((lastStyle = (StyleRange) styles.lastElement()).fontStyle
						== SWT.BOLD)) {
				int start = scanner.getStartOffset() + event.lineOffset;
				lastStyle = (StyleRange) styles.lastElement();
				// A font style of SWT.BOLD implies that the last style
				// represents a java keyword.
				if (lastStyle.start + lastStyle.length == start) {
					// Have the white space take on the style before it to 
					// minimize the number of style ranges created and the
					// number of font style changes during rendering.
					lastStyle.length += scanner.getLength();
				}
			}
			token = scanner.nextToken();
		}
		event.styles = new StyleRange[styles.size()];
		styles.copyInto(event.styles);
	}

	public void parseBlockComments(String text) {
		blockComments = new Vector();
		blockCommentsJmlMultiLine = new Vector();
		blockCommentsJmlSingleLine = new Vector();
		Vector style = null;
		StringReader buffer = new StringReader(text);
		int ch;
		boolean blkCommentM = false;
		boolean blkCommentS = false;
		int cnt = 0;
		int[] offsets = new int[2];
		boolean done = false;

		try {
			while (!done) {
				switch (ch = buffer.read()) {
					case -1 :
						{
							if (blkCommentM || blkCommentS) {
								offsets[1] = cnt;
								style.addElement(offsets);
							}
							done = true;
							break;
						}
					case '/' :
						{
							ch = buffer.read();
							if ((ch == '*')
								&& (!(blkCommentM || blkCommentS))) {
								ch = buffer.read();
								if (ch == '@')
									style = blockCommentsJmlMultiLine;
								else
									style = blockComments;
								offsets = new int[2];
								offsets[0] = cnt;
								blkCommentM = true;
								cnt++;
								cnt++;
							} else if (
								(ch == '/')
									&& (!(blkCommentM || blkCommentS))) {
								ch = buffer.read();
								if (ch == '@')
									style = blockCommentsJmlSingleLine;
								else
									style = blockComments;
								offsets = new int[2];
								offsets[0] = cnt;
								blkCommentS = true;
								cnt++;
								cnt++;
							} else {
								cnt++;
							}
							cnt++;
							break;
						}
					case '\n' :
						{
							if (blkCommentS) {
								blkCommentS = false;
								offsets[1] = cnt;
								style.addElement(offsets);

							}
							cnt++;
							break;
						}
					case '*' :
						{
							if (blkCommentM) {
								ch = buffer.read();
								cnt++;
								if (ch == '/') {
									blkCommentM = false;
									offsets[1] = cnt;
									style.addElement(offsets);
								}
							}
							cnt++;
							break;
						}
					default :
						{
							cnt++;
							break;
						}
				}
			}
		} catch (IOException e) { // ignore errors
		}
	}
}

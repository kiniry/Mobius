//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Box.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.viewer.source;

import jack.plugin.perspective.ISourceCaseViewer;

import java.io.IOException;

import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

import org.eclipse.swt.custom.StyledText;

/**
 * This class describes a colored information in the source text. It corresponds 
 * to an highlighted box with a associated information.
 * @author L. Burdy
 */
public class Box {

	private int index;

	/**
	 * The line number of the colored info.
	 **/
	private int line;

	/**
	 * The column number of the colored info.
	 **/
	private int column;

	/**
	 * The length of the colored box.
	 **/
	private int length;

	/**
	 * The index of the comment associated with this box. Each index corresponds 
	 * to a comment.
	 **/
	private byte comment;

	/**
	 * The complementary information displayed.
	 **/
	private String info;

	//	/**
	//	 * The highlighted formula.
	//	 **/
	//	private Formula f;

	/**
	 * Array of displayed information.
	 **/
	private static String[][] commentText = { { "is true", "is_false" }, {
			"is not castable",
				"is negative",
				"is null",
				"equals 0",
				"is not storable",
				"is out of bounds",
				"throws exception",
				"catches" },
				{
			"", "creates " }
	};

	/**
	 * The green color.
	 **/
	public static org.eclipse.swt.graphics.Color GREEN =
		new org.eclipse.swt.graphics.Color(null, 10, 220, 10);

	/**
	 * The red color.
	 **/
	private static org.eclipse.swt.graphics.Color RED =
		new org.eclipse.swt.graphics.Color(null, 220, 10, 10);

	/**
	 * The blue color.
	 **/
	private static org.eclipse.swt.graphics.Color BLUE =
		new org.eclipse.swt.graphics.Color(null, 50, 0, 255);

	/**
	 * Constructs a box from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream associated with the .jpo file
	 * @param f The formula corresponding to this box
	 * @throws IOException
	 **/
	public Box(JpoInputStream s) throws IOException {
		index = s.readInt();
		line = s.readInt();
		column = s.readInt();
		length = s.readInt();
		comment = s.readByte();
		info = s.readUTF();
		//		this.f = f;
	}

	/**
	 * Tests whether a point belongs to the box.
	 * @param text The current displayed text.
	 * @param x The abscissa of the point
	 * @param y The ordinate of the point
	 * @return <code>true</code> if the point belongs to the box, 
	 * <code>false</code> otherwise
	 **/
	boolean includes(StyledText text, int x, int y) {
		int start = text.getOffsetAtLine(line) + column;
		return text.getLocationAtOffset(start).x <= x
			&& x <= text.getLocationAtOffset(start + length + 1).x
			&& text.getLocationAtOffset(start).y <= y
			&& y <= text.getLocationAtOffset(start).y + 12;
	}

	public boolean in(StyledText text, int offset) {
		int start = text.getOffsetAtLine(line) + column;
		return start <= offset && offset <= start + length;
	}

	public int getXOffset(StyledText text) {
		return text.getOffsetAtLine(line) + column;
	}

	public int getYOffset(StyledText text) {
		return text.getOffsetAtLine(line) + column + length;
	}

	/**
	 * Saves the box to a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>.
	 * @param s The output stream of the .jpo file
	 * @throws IOException
	 **/
	public void save(JpoOutputStream s, int index) throws IOException {
		s.writeInt(index);
		s.writeInt(line);
		s.writeInt(column);
		s.writeInt(length);
		s.writeByte(comment);
		s.writeUTF(info);
	}

	/**
	 * Tries to highlight the box in the given text.
	 * @param text The current source code text.
	 * @param color The color in which the box is highlighted
	 * @param start The point in the text where the box begin
	 * @return <code>true</code> if the box is a valid box for the current and 
	 * if it corresponds to blue or red information, <code>false</code> 
	 * otherwise
	 **/
	private boolean highlightBox(
		ISourceCaseViewer text,
		org.eclipse.swt.graphics.Color fgcolor,
		org.eclipse.swt.graphics.Color bgcolor) {
		return text.highlight(fgcolor, bgcolor, line, column, length)
			&& comment != 0;
	}

	/**
	 * Tries to highlight the box in the given text.
	 * @param display The current display.
	 * @param text The current source code text.
	 * @return <code>true</code> if the box is a valid box for the current and 
	 * if it corresponds to blue or red information, <code>false</code> 
	 * otherwise
	 **/
	public boolean highlightBox(ISourceCaseViewer text) {
		org.eclipse.swt.graphics.Color bgc = null;
		org.eclipse.swt.graphics.Color fgc = null;
		if (comment == 0)
			fgc = GREEN;
		else if (comment > 10 && comment <= 20)
			bgc = RED;
		else
			fgc = BLUE;
		if (comment != -1)
			try {
				return highlightBox(text, fgc, bgc);
			} catch (IllegalArgumentException iae) {
			}
		return false;
	}

	/**
	 * Returns the text location abscissa corresponding to the right edge of the 
	 * box.
	 * @return the text location abscissa corresponding to the right edge of 
	 * the box.
	 **/
	int getX(StyledText text) {
		return text.getLocationAtOffset(
			text.getOffsetAtLine(line) + column + length + 1).x;
	}

	/**
	 * Returns the text location ordinate corresponding to the top edge of the 
	 * box.
	 * @return the text location ordinate corresponding to the top edge of 
	 * the box
	 **/
	int getY(StyledText text) {
		return text.getLocationAtOffset(text.getOffsetAtLine(line) + column).y;
	}

	/**
	 * Returns the information associated with the box.
	 * @return the displayed information corresponding to the comment index 
	 * plus the additionnal information if it exists.
	 **/
	public String getCommentText() {
		if (comment <= 20)
			return commentText[comment / 10][comment % 10 - 1];
		else
			return commentText[comment / 10][comment % 10 - 1] + info;
	}

	//	/**
	//	 * Returns the formula associated with the box.
	//	 * @return <code>f</code>
	//	 **/
	//	Formula getFormula() {
	//		return f;
	//	}

	/**
	 * @return
	 */
	public int getLength() {
		return length;
	}

	/**
	 * @return
	 */
	public int getIndex() {
		return index;
	}

}

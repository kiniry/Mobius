//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ParsedItem.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/*******************************************************************************/
package jml2b.structure.java;
import java.io.IOException;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import jml.LineAST;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;
import antlr.collections.AST;

/**
 * This class provides features to store informations that allow to locate a 
 * parsed items.
 * Those informations are the file where the item is located, with the line, the 
 * column and its length. 
 * @author L. Burdy
 */
public class ParsedItem extends Profiler implements Serializable {

	public final static ParsedItem $empty = new ParsedItem();
	
	/**
	 * Line number where is located the item.
	 **/
	private int line;

	/**
	 * Column number where the item is located.
	 **/
	private int column;

	/**
	 * Length of the item.
	 **/
	private int length;

	/**
	 * File where the item is located.
	 **/
	private JmlFile jmlFile;

	/**
	 * Constructs a default item.
	 **/
	public ParsedItem() {
	}

	/**
	 * Constructs an item from a <i>JML file</i>.
	 * @param jf The file
	 **/
	public ParsedItem(JmlFile jf) {
		jmlFile = jf;
	}

	/**
	 * Constructs an item from a <i>JML file</i> and an <code>AST</code> node.
	 * @param jf The file
	 * @param tree The <code>AST</code> node from which the line, the column and
	 * the length are extracted
	 **/
	public ParsedItem(JmlFile jf, AST tree) {
		if (jf != null) {
			jmlFile = jf;
			if (tree instanceof LineAST) {
				line = ((LineAST) tree).line - 1;
				column = ((LineAST) tree).column - 1;
			} else {
				line = 0;
				column = 0;
			}
			length = tree.getText().length();
		}
	}

	/**
	 * Constructs an item from another.
	 * @param b The item where informations are collected
	 **/
	//@ requires b != null;
	public ParsedItem(ParsedItem b) {
		setBox(b);
	}

	/**
	 * Deines an item from another.
	 * @param b The item where informations are collected
	 **/
	//@ requires b != null;
	public final void setBox(ParsedItem b) {
		jmlFile = b.jmlFile;
		line = b.line;
		column = b.column;
		length = b.length;
	}

	/**
	 * Saves the item in a <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s output stream for the jpo file
	 * @throws IOException
	 **/
	//@ requires s != null;
	public final void save(JpoOutputStream s) throws IOException {
		s.writeInt(line);
		s.writeInt(column);
		s.writeInt(length);
	}

	/**
	 * Returns the line.
	 * @return <code>line</code>
	 **/
	public final int getLine() {
		return line;
	}

	/**
	 * Returns the column.
	 * @return <code>column</code>
	 **/
	public final int getColumn() {
		return column;
	}

	/**
	 * Returns the file.
	 * @return <code>jmlFile</code>
	 **/
	public final JmlFile getJmlFile() {
		return jmlFile;
	}

	public final void change(ParsedItem pi) {
		column = pi.column;
		jmlFile = pi.jmlFile;
		length = pi.length;
		line = pi.line;
	}

	public final void change(Vector pi) {
		column = Integer.MAX_VALUE;
		length = 0;
		line = Integer.MAX_VALUE;
		Enumeration e = pi.elements();
		while (e.hasMoreElements()) {
			ParsedItem element = (ParsedItem) e.nextElement();
			if (element.column <= column)
				column = element.column;
			jmlFile = element.jmlFile;
			length += element.length;
			if (element.line <= line)
				line = element.line;
		}
	}

	static final long serialVersionUID = -2308775037213438489L;

}
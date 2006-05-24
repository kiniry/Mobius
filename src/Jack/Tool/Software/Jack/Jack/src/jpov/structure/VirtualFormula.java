//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: VirtualFormula
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;
import jpov.viewer.source.Box;

/**
 * This class implements a formula with its corresponding set of boxes.
 * @author L. Burdy
 **/
public class VirtualFormula {

	/**
	 * Index of the formula (used to find it in the hypothesis array
	 **/
	private int index;

	/**
	 * The formula
	 **/
	private Formula f;

	/**
	 * Set of box associated to the formula
	 **/
	private Vector flow;

	/**
	 * The origin of the formula
	 **/
	private byte origin;

	/*@
	  @ private invariant f != null
	  @                && flow != null
	  @                && flow.elementType <: \type(Box);
	  @*/

	/**
	 * Constructs a virtual formula from a loaded
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the jpo file
	 **/
	VirtualFormula(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		index = s.readInt();
		origin = s.readByte();
		f = Formula.create(config, s, fi);
		int size = s.readInt();
		flow = new Vector();
		for (int i = 0; i < size; i++)
			flow.add(new Box(s));
	}

	/**
	 * Saves the virtual formula into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream corresponding to the jpo file
	 * @param index The index of the virtual formula into the hypothesis array
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, int index, IJmlFile jf) throws IOException {
		this.index = index;
		s.writeInt(index);
		s.writeByte(origin);
		f.save(config, s, jf);
		s.writeInt(flow.size());
		Enumeration e = flow.elements();
		while (e.hasMoreElements()) {
			Box element = (Box) e.nextElement();
			element.save(s, 0);
		}
	}
	/**
	 * Converts the current formula to a string suitable for output into
	 * the Java view.
	 * @param indent The current indentation
	 * @return the converted formula into Java language
	 **/
	public String toLangDefault(int indent) {
		return f.toLangDefault(indent);
	}
	/**
	 * Converts the current formula to a string suitable for output into
	 * the Java view.
	 * @deprecated
	 * @param indent The current indentation
	 * @return the converted formula into Java language
	 **/
	public String toJava(int indent) {
		return f.toLangDefault(indent);
	}

	//	/**
	//	 * Converts the current formula to a string suitable for output to
	//	 * the Atelier B.
	//	 * @param indent The current indentation
	//	 * @param view Indicates whether the formula is displayed into the view or
	//	 * into the jpo file.
	//	 * @return the converted formula into B language
	//	 **/
	//	public String toDisplayedB(int indent) {
	//		try {
	//			return f.toLang("BDisplayed", indent).toUniqString();
	//		} catch (LanguageException le) {
	//			throw new InternalError(le.getMessage());
	//		}
	//	}

	//	public String toB(int indent) {
	//		try {
	//			return f.toLang("B", indent).toUniqString();
	//		} catch (LanguageException le) {
	//			throw new InternalError(le.getMessage());
	//		}
	//	}

	// Currently ignore indent
	//	public ITranslationResult toSimplify(int indent) {
	//		try {
	//			return f.toLang("Simplify", indent);
	//		} catch (LanguageException le) {
	//			throw new InternalError(le.getMessage());
	//		}
	//	}

	/**
	 * Returns the index of the formula
	 * @return <code>index</code>
	 **/
	int getIndex() {
		return index;
	}

	/**
	 * Returns the f.
	 * @return Formula
	 */
	public Formula getF() {
		return f;
	}

	/**
	 * Returns the set of box associated to the formula.
	 */
	public Enumeration getFlow() {
		return flow.elements();
	}

	/**
	 * Returns the origin.
	 * @return byte
	 */
	public byte getOrigin() {
		return origin;
	}

}

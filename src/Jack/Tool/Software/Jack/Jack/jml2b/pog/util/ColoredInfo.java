//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ColoredInfo.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.util;

import java.io.IOException;
import java.io.Serializable;

import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class defines informations associated to formula in order to color the
 * code in the viewer.
 * @author L. Burdy
 */
public class ColoredInfo extends Profiler implements Serializable {

	/**
	 * comment indice corresponding to a test considered as true (blue).
	 **/
	public static final byte IS_TRUE = 1;

	/**
	 * comment indice corresponding to a test considered as false (blue).
	 **/
	public static final byte IS_FALSE = 2;

	/**
	 * comment indice corresponding to a ClassCastException (red).
	 **/
	public static final byte IS_NOT_CASTABLE = 11;

	/**
	 * comment indice corresponding to a NegativeArraySizeException (red).
	 **/
	public static final byte IS_NEGATIVE = 12;

	/**
	 * comment indice corresponding to a NullPointerException (red).
	 **/
	public static final byte IS_NULL = 13;

	/**
	 * comment indice corresponding to a ArithmeticException (red).
	 **/
	public static final byte EQUALS_0 = 14;

	/**
	 * comment indice corresponding to a ArrayStoreException (red)
	 **/
	public static final byte IS_NOT_STORABLE = 15;

	/**
	 * comment indice corresponding to a ArrayIndexOutOfBoundException (red)
	 **/
	public static final byte IS_OUT_OF_BOUNDS = 16;

	/**
	 * comment indice corresponding to an exception thrown by a method call 
	 * (red)
	 **/
	public static final byte THROWS_EXCEPTION = 17;

	/**
	 * comment indice corresponding to the call of a method (blue).
	 **/
	public static final byte METHOD_CALL = 21;

	/**
	 * comment indice corresponding to an object creation (blue).
	 **/
	public static final byte NEW = 22;

	private int index;

	/**
	 * Parsed item that is colored.
	 **/
	private ParsedItem pi;

	/**
	 * comment indice of the item:
	 * <UL>
	 * <li> -1     means no color displayed
	 * <li>  0     means green color
	 * <li> 1..2   means blue color
	 * <li> 11..18 means red color
	 * <li> 21..22 means blue color with associated informations
	 * </UL>
	 **/
	private byte comment;

	/**
	 * Informations associated with comment indices METHOD_CALL or NEW.
	 * This information is the specification of called method.
	 **/
	private String info = "";

	/*@
	  @ private invariant pi != null;
	  @                && info != null;
	  @*/

	/**
	 * Constructs a colored info with no coloration.
	 **/
	public ColoredInfo() {
		pi = new ParsedItem();
		comment = -1;
	}

	/**
	 * Constructs a <i>green</i> colored info
	 **/
	/*@ 
	  @ requires b != null;
	  @*/
	public ColoredInfo(ParsedItem b) {
		pi = b;
		comment = 0;
		info = "";
	}

	/**
	 * Constructs a <i>red</i> colored info or a <i>blue</i> without additional 
	 * informations.
	 **/
	/*@
	  @ requires b != null;
	  @*/
	public ColoredInfo(ParsedItem b, byte c) {
		pi = b;
		comment = c;
		info = "";
	}

	/**
	 * Constructs a <i>blue</i> colored info with informations.
	 **/
	/*@ 
	  @ requires b != null;
	  @*/
	public ColoredInfo(ParsedItem b, byte c, String s) {
		pi = b;
		comment = c;
		info = s;
	}

	//	/**
	//	 * Loads the colored info from a 
	//	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	//	 **/
	//	public ColoredInfo(JpoInputStream s) throws IOException {
	//		index = s.readInt();
	//		new ParsedItem(s);
	//		s.readByte();
	//		s.readUTF();
	//		this.pi = new ParsedItem();
	//		this.comment = -1;
	//	}

	/**
	 * Saves the colored info in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a> if it is 
	 * declared in a specified JML file
	 * @param s output stream for the jpo files
	 * @param jf current {@link JmlFile}
	 * @throws IOException
	 * @see VirtualFormula#save(DataOutputStream, int, JmlFile)
	 * @see Theorem#save(DataOutputStream, JmlFile)
	 **/
	//@ requires s != null;
	public void save(JpoOutputStream s, int index, JmlFile f)
		throws IOException {
		this.index = index;
		s.writeInt(index);
		pi.save(s);
		if (f != pi.getJmlFile())
			s.writeByte(-1);
		else
			s.writeByte(comment);
		s.writeUTF(info);
	}

	static final long serialVersionUID = -2308775037213438489L;

	public int getIndex() {
		return index;
	}

	/**
	 * @return
	 */
	public byte getComment() {
		return comment;
	}

}
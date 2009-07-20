//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: GoalOrigin.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;

import jml2b.exceptions.LoadException;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class describes the origin of a goal.
 * @author L. Burdy
 */
public class GoalOrigin {

	/**
	 * Goal origin value that corresponds to the proof of a static invariant.
	 **/
	public static final byte STATIC_INVARIANT = 0;

	/**
	 * Goal origin value that corresponds to the proof of a non static invariant.
	 **/
	public static final byte MEMBER_INVARIANT = 1;

	/**
	 * Goal origin value that corresponds to the proof of an <i>ensures</i>
	 * clause.
	 **/
	public static final byte ENSURES = 2;

	/**
	 * Goal origin value that corresponds to the proof of a <i>requires</i>
	 * clause.
	 **/
	public static final byte REQUIRES = 3;

	/**
	 * Goal origin value that corresponds to the proof of the initialization
	 * of a loop invariant.
	 **/
	public static final byte LOOP_INVARIANT_INIT = 4;

	/**
	 * Goal origin value that corresponds to the proof of an <i>exsures</i>
	 * clause.
	 **/
	public static final byte EXSURES = 5;

	/**
	 * Goal origin value that corresponds to the proof of an <i>exsures</i>
	 * clause of a loop.
	 **/
	public static final byte LOOP_EXSURES = 6;

	/**
	 * Goal origin value that corresponds to the proof of a <i>modifies</i>
	 * clause.
	 **/
	public static final byte MODIFIES = 7;

	/**
	 * Goal origin value that corresponds to the proof of the <i>requires</i>
	 * clause of the super method.
	 **/
	public static final byte SUPER_REQUIRES = 8;

	/**
	 * Goal origin value that corresponds to the proof of an assertion.
	 **/
	public static final byte ASSERT = 9;

	/**
	 * Goal origin value that corresponds to the proof of a <i>requires</i> 
	 * clause of a specified block.
	 **/
	public static final byte BLOCK_REQUIRES = 10;

	/**
	 * Goal origin value that corresponds to the proof of an <i>exsures</i> 
	 * clause of a specified block.
	 **/
	public static final byte BLOCK_EXSURES = 11;

	/**
	 * Goal origin value that corresponds to the proof of an <i>ensures</i> 
	 * clause of a specified block.
	 **/
	public static final byte BLOCK_ENSURES = 12;

	/**
	 * Goal origin value that corresponds to the proof of a loop variant.
	 **/
	public static final byte LOOP_VARIANT = 13;

	public static final byte WELL_DEFINED = 14;

	public static final byte STATIC_CONSTRAINT = 15;

	public static final byte INSTANCE_CONSTRAINT = 16;

	/**
	 * Goal origin value that corresponds to the proof of the preservation
	 * of a loop invariant.
	 **/
	public static final byte LOOP_INVARIANT_PRESERVE = 17;

	/**
	 * Number of goal origin types.
	 **/
	private static final byte MAXGOALTYPE = 18;

	/**
	 * Returns the number of goal origin types.
	 * @return <code>MAXGOALTYPE</code>
	 **/
	//@ ensures \result == MAXGOALTYPE;
	public static int /*@ pure */
	getMaxGoalType() {
		return GoalOrigin.MAXGOALTYPE;
	}

	/**
	 * Returns a string describing the goal origin.
	 * @param type The goal origin
	 * @param comment The comment associated with the origin
	 * @return a string to be displayed in manner to give informations about 
	 * the goal origin.
	 **/
	public static String getGoalTypeString(byte type, String comment) {
		switch (type) {
			case GoalOrigin.WELL_DEFINED :
				return "Check well definedness";
			case GoalOrigin.STATIC_INVARIANT :
				return "Check static invariant";
			case GoalOrigin.MEMBER_INVARIANT :
				return "Check member invariant";
			case GoalOrigin.ENSURES :
				return "Check ensures clause of the current method";
			case GoalOrigin.REQUIRES :
				return "Check requires clause of the called method " + comment;
			case GoalOrigin.LOOP_INVARIANT_INIT :
				return "Check initialisation of loop invariant";
			case GoalOrigin.LOOP_INVARIANT_PRESERVE :
				return "Check preservation of loop invariant";
			case GoalOrigin.LOOP_VARIANT :
				return "Check the variant of the loop";
			case GoalOrigin.EXSURES :
				return "Check exsures clause of the method " + comment;
			case GoalOrigin.LOOP_EXSURES :
				return "Check the exsures clause of the loop";
			case GoalOrigin.MODIFIES :
				if (comment.equals(""))
					return "Check modifies clause";
				else
					return "Check modifies clause concerning the field "
						+ comment;
			case GoalOrigin.SUPER_REQUIRES :
				return "Check requires clause of the super method";
			case GoalOrigin.ASSERT :
				return "Check assertion";
			case GoalOrigin.BLOCK_REQUIRES :
				return "Check block requires";
			case GoalOrigin.BLOCK_ENSURES :
				return "Check ensures clause of the block";
			case GoalOrigin.BLOCK_EXSURES :
				return "Check exsures clause of the block";
			case STATIC_CONSTRAINT :
				return "Check static constraint clause";
			case INSTANCE_CONSTRAINT :
				return "Check instance constraint clause";
			default :
				return "";
		}
	}

	/**
	 * The origin of the goal.
	 **/
	private byte origin;

	/**
	 * The comment associated with the origin. It can the name of a field for
	 * a modifies goal or a method signature for a requires goal.
	 */
	private String comment;

	/**
	 * Constructs a goal origin from a loaded
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the jpo file
	 **/
	public GoalOrigin(JpoInputStream s) throws IOException, LoadException {
		origin = s.readByte();
		comment = s.readUTF();
	}

	/**
	 * Constructs a goal origin for a modifies
	 * @param origin The origin
	 * @param f The modified field
	 */
	public GoalOrigin(byte origin, AField f) {
		this.origin = origin;
		comment = f.getName();
	}

	/**
	 * Constructs a goal origin for a requires
	 * @param origin The origin 
	 * @param m The called method
	 */
	public GoalOrigin(byte origin, AMethod m) {
		this.origin = origin;
		comment = m.getName() + m.getSignature();
	}

	/**
	 * Constructs a goal origin with no comment
	 * @param origin The origin 
	 */
	public GoalOrigin(byte origin) {
		this.origin = origin;
		comment = "";
	}

	/**
	 * Saves the goal origin in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream representing the jpo file.
	 * @throws IOException
	 **/
	public void save(JpoOutputStream s) throws IOException {
		s.writeByte(origin);
		s.writeUTF(comment);
	}

	/**
	 * Returns the origin of the goal.
	 * @return <code>origin</code>
	 */
	public byte getOrigin() {
		return origin;
	}

}

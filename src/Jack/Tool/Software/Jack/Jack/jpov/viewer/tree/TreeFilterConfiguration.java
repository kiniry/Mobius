//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeFilterConfiguration.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jml2b.pog.lemma.GoalOrigin;

/**
 * Class containing the configuration for a TreeFilterWindow.
 * @author L. Burdy, A. Requet
 **/
public class TreeFilterConfiguration {

	/** 
	 * The name of the configuration. 
	 */
	String name;

	/**
	 * Indicates whether the proved items must be displayed or not.
	 **/
	boolean showProved;

	/**
	 * Indicates whether the unproved items must be displayed or not.
	 **/
	boolean showUnProved;

	/**
	 * Upper proof percentage bound for a class to be displayed 
	 **/
	int classPercent;

	/**
	 * Upper proof percentage bound for a method to be displayed 
	 **/
	int methodPercent;

	/**
	 * Upper proof percentage bound for a case to be displayed 
	 **/
	int casesPercent;

	/**
	 * Indicates whether some goal types are not displayed
	 **/
	boolean showGoalType;

	/**
	 * Arrays of goal type indicating for each one if it should be displayed
	 * or not. It is only valid when showGoalType is true.
	 **/
	boolean[] showTypes;

	//@ invariant showTypes != null;
	//@ invariant showTypes.length == GoalStatus.MAXGOALTYPE;

	/**
	 * Creates a new TreeFilterConfiguration with the given name 
	 * <code>n</code>.
	 */
	public TreeFilterConfiguration(String n) {
		name = n;
		showProved = false;
		showUnProved = true;
		classPercent = 99;
		methodPercent = 99;
		casesPercent = 99;
		showGoalType = false;
		showTypes = new boolean[GoalOrigin.getMaxGoalType()];
		// do not fill the content of the array manually, since Java 
		// automatically initialize the content of the array to false.
		//      for (int i = 0; i < GoalStatus.getMaxGoalType(); i++) {
		//          showTypes[i] = false;
		//      }
	}

	/**
	 * Constructs a tree filter configuration
	 * @param n The name of the configuration
	 * @param show_proved indicates whether the proved items must be displayed 
	 * or not
	 * @param show_unproved indicates whether the unproved items must be 
	 * displayed or not.
	 * @param class_percent The upper proof percentage bound for a class to be 
	 * displayed 
	 * @param method_percent The upper proof percentage bound for a method to 
	 * be displayed 
	 * @param cases_percent The upper proof percentage bound for a case to be 
	 * displayed 
	 **/
	public TreeFilterConfiguration(
		String n,
		boolean show_proved,
		boolean show_unproved,
		int class_percent,
		int method_percent,
		int cases_percent) {
		name = n;
		showProved = show_proved;
		showUnProved = show_unproved;
		classPercent = class_percent;
		methodPercent = method_percent;
		casesPercent = cases_percent;

		showGoalType = false;
		showTypes = new boolean[GoalOrigin.getMaxGoalType()];
	}

	/**
	 * The default configuration <i>Show all</i>.
	 */
	public static final TreeFilterConfiguration SHOW_ALL =
		new TreeFilterConfiguration("Show all", true, true, 100, 100, 100);

	/**
	 * The default configuration <i>Show unproved</i>.
	 **/
	public static final TreeFilterConfiguration SHOW_UNPROVED =
		new TreeFilterConfiguration("Show unproved", false, true, 100, 99, 99);

	public static final TreeFilterConfiguration SHOW_CASES =
		new TreeFilterConfiguration("Show cases", false, false, 100, 100, 100);
}

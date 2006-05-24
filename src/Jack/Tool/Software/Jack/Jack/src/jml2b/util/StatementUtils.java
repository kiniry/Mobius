//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StatementUtils.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.util;

import java.util.Enumeration;

import jml2b.structure.statement.Expression;

/**
 * Utility class for handling statement operations
 * @author L. Burdy, A. Requet
 */
public class StatementUtils extends Profiler {

	/** 
	 * Return an expression corresponding to the "and" of all the expression
	 * enumerated. Returns <code>null</code> in case where e is an empty 
     * enumeration.
     * @param e The set of expressions
	 */
	//@ requires e != null && e.elementType <: \type(Expression);
	public static Expression andEnumeration(Enumeration e) {
		Expression res = null;
		while (e.hasMoreElements()) {
			Expression s = (Expression) e.nextElement();
			res = res == null ? s : Expression.and(res, s);
		}
		return res;
	}

}

//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LinkUtils.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.link;

import java.util.Enumeration;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.TypeCheckException;
import jml2b.util.Profiler;

/**
 * @author A. Requet, L. Burdy
 */
public class LinkUtils extends Profiler {
	/** 
	 * Links all the Linkable elements provided by the enumeration e using
	 * LinkContext f.
	 * 
	 * return the number of errors encountered.
	 */
	/*@
	  @ requires e != null;
	  @*/
	public static int linkEnumeration(
		IJml2bConfiguration config,
		Enumeration e,
		LinkContext f)
		throws Jml2bException {
		int error_count = 0;
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			Linkable l = (Linkable) e.nextElement();
			try {
				l.link(config, f);
			} catch (LinkException ex) {
				ErrorHandler.error(
					f.jmlFile,
					ex.getLine(),
					ex.getColumn(),
					ex.getMessage());
				++error_count;
			}
		}
		return error_count;
	}

	/*@
	  @ requires e != null;
	  @*/
	public static int linkStatements(
		IJml2bConfiguration config,
		Enumeration e,
		LinkContext f)
		throws Jml2bException {
		int error_count = 0;
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			Linkable l = (Linkable) e.nextElement();
			try {
				error_count += l.linkStatements(config, f);
			} catch (LinkException ex) {
				ErrorHandler.error(
					f.jmlFile,
					ex.getLine(),
					ex.getColumn(),
					ex.getMessage());
				++error_count;
			}
		}
		return error_count;
	}

	public static int typeCheckEnumeration(
		IJml2bConfiguration config,
		Enumeration e,
		LinkContext f)
		throws Jml2bException {
		int error_count = 0;
		/*@ 
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		while (e.hasMoreElements()) {
			TypeCheckable l = (TypeCheckable) e.nextElement();
			try {
				l.typeCheck(config, f);
			} catch (TypeCheckException ex) {
				ErrorHandler.error(
					f.jmlFile,
					ex.getLine(),
					ex.getColumn(),
					ex.getMessage());
				++error_count;
			}
		}
		return error_count;
	}

}

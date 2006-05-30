//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimplifyException.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package simplifyPlugin;

/**
 * @author A. Requet
 */
public class SimplifyException extends Exception {
	/**
	 * 
	 */
	private static final long serialVersionUID = 2247623800372719020L;

	public SimplifyException(String description)
	{
		super(description);
	}
}

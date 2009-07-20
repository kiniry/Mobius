//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package pvsPlugin;

/**
 * @author A. Requet
 */
public class PvsException extends Exception {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public PvsException(String description)
	{
		super(description);
	}
}

//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.pog.printers;

import java.io.File;
import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.JmlFile;

/**
 * This interface defines a printer for a plugin.
 * 
 * @author L. Burdy
 **/
public interface IPrinter {

	/**
	 * The array of builtin types name
	 **/
	public static final String[] builtinNames =
		{ "c_int", "c_short", "c_char", "c_byte", "c_boolean" };

	/**
	 * Writes an output file corresponding to the entry of a prover.
	 * @param printer The parent printer
	 * @param fi The jpo file
	 * @param output_directory The output_directory.
	 * @throws IOException
	 **/
	void print(
			IJml2bConfiguration config, 
		IClassResolver printer,
		JmlFile fi,
		File output_directory)
		throws IOException;
}

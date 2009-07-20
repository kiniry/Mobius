//******************************************************************************
//* Copyright (c) 2003 INRIA. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: 
//*
//*******************************************************************************
//* Warnings/Remarks:
//******************************************************************************/

package jml2b.util;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

import jml2b.Jml2b;
import jml2b.Jml2bConfig;
import jml2b.structure.java.JmlFile;

/**
 * @author L. Burdy
 **/
public class Emitter {

	/**
	 * Displays the usage
	 **/
	public static void displayUsage() {
		displayUsage(System.out);
	}
	public static void displayUsage(PrintStream out) {
		out.println("Usage:");
		out.println(
			" java jml2b/util/Emitter ast_files output_directory");
		out.println();
	}

	public static void main(String[] args) {
		File output_directory = null;
		String[] jmlPath = null;
		boolean obviousPo;

		if (args.length < 1) {
			displayUsage();
			System.exit(0);
		}

		// get the file name that is used for loading properties
		try {
			Jml2b.loadProperties();
		} catch (IOException e) {
			Logger.err.println("Error loading property file");
		}

		// get the file_in property first, since if it is nonnull, then
		// the app can be launched without arguments
		System.getProperty(Jml2b.inFileProperty);

		// initialize jml search path
		String jml_path_list = System.getProperty(Jml2b.jmlPathProperty);
		if (jml_path_list != null) {
			jmlPath = Util.tokenize(jml_path_list, File.pathSeparator);
		}

		obviousPo = false;
		String obvious_po_string = System.getProperty(Jml2b.obviousPoProperty);
		if (obvious_po_string != null)
			obviousPo = obvious_po_string.equals("true");

		JmlFile[] files;
		Jml2bConfig config = new Jml2bConfig(jmlPath, obviousPo);

		Logger.err.print("Loading ast file...");
		files = Jml2b.loadAstImage(config, args[0]);
		output_directory = Jml2b.getOutputDir(args[args.length - 1]);
		if (output_directory == null) {
			System.exit(1);
		}
		for (int i = 0; i < files.length; i++) {
			File f =
				new File(output_directory, files[i].getFlatName(config.getPackage()) + ".java");
			try {
				DataOutputStream stream =
					new DataOutputStream(
						new BufferedOutputStream(new FileOutputStream(f)));
				stream.writeUTF(files[i].emit(config));
				stream.close();
			} catch (IOException ioe) {
				;
			}
		}
	}
}

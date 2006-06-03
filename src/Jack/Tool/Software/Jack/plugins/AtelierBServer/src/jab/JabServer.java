///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: JabServer
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jab;

import java.rmi.Naming;
import java.io.*;
import java.util.Properties;

public class JabServer {

	static final String Version = "v1_3";

	static String propertyFileProperty = "jab.propertyfile";
	// default property file that is read.
	static String propertyFile = "jab.properties";

	JabServer() {
		try {
			Jab ab = new Jab();
			System.out.println(ab.toString() + "created");
			System.out.println(Jab.DIR);
			Naming.rebind("rmi://saule:1099/JabService_" + Version, ab);
		} catch (Exception e) {
			System.err.println("Trouble " + e);
		}
	}

	public static void main(String[] args) {
		try {
			loadPropertiesFile();
		} catch (IOException e) {
			System.err.println("Error loading property file");
		}

		Jab.setDir(System.getProperty("jab.B_projects_directory"));
		Jab.setBbatch(System.getProperty("jab.bbatch_exe"));
		Jab.setAb(System.getProperty("jab.AB_directory"));
		Jab.setAbdef(System.getProperty("jab.ab_def"));
		Jab.setVersion(System.getProperty("jab.AB_version"));
		Jab.setResourceFile(System.getProperty("jab.AB_resource_file"));
		Jab.setExec();
		new JabServer();
	}

	static void loadPropertiesFile() throws IOException {

		File f = getPropertyFile();
		if (f != null) {
			FileInputStream s = new FileInputStream(f);
			Properties props = new Properties(System.getProperties());
			props.load(s);
			s.close();
			System.setProperties(props);
		}
	}

	private static File getPropertyFile() {
		File result;
		// first, look if a file is given on the command line
		String cmd_line_file = System.getProperty(propertyFileProperty);
		if (cmd_line_file != null) {
			result = new File(cmd_line_file);
			if (result.exists()) {
				return result;
			}
			System.err.println(
				"The property file " + cmd_line_file + " does not exists");
			System.exit(1);
		}

		// look for the file in the current directory
		result = new File(propertyFile);
		if (result.exists()) {
			return result;
		}

		// look for the file in the user's home directory
		result =
			new File(
				System.getProperty("user.home")
					+ File.separator
					+ propertyFile);

		if (result.exists()) {
			return result;
		}
		System.err.println("No property file have been found.");
		System.exit(1);
		return null;
	}

}

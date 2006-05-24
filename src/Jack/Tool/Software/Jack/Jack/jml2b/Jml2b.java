//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Jml2b.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Properties;

import jml.LineAST;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.StderrHandler;
import jml2b.pog.Pog;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Package;
import jml2b.util.JmlEntryFile;
import jml2b.util.Profiler;
import jml2b.util.Util;
import antlr.collections.AST;

/** 
 * @author L. Burdy, A. Requet
 */
public class Jml2b extends Profiler {

	static String propertyFileProperty = "jml2b.propertyfile";

	/**
	 * default property file that is read.
	 **/
	static String propertyFile = "jml2b.properties";

	static String baseFileProperty = "jml2b.basefile";

	static String displayStatsProperty = "jml2b.stats";

	public static String jmlPathProperty = "jml2b.jmlpath";

	/**
	 * if this property is set, then load the state from the given infile.
	 **/
	public static String inFileProperty = "jml2b.infile";

	/** 
	 * if this property is set, then save the state to the given file after
	 * loading.
	 **/
	static String outFileProperty = "jml2b.outfile";

	static String debugProperty = "jml2b.debug";

	public static String obviousPoProperty = "jml2b.obviouspo";

	/**
	 * Displays the usage
	 **/
	public static void displayUsage() {
		System.out.println("Usage:");
		System.out.println(" java jml2b/Jml2b -ast ast_files output_directory");
		System.out.println(" java jml2b/Jml2b Java_files output_directory");
		System.out.println(" java jml2b/Jml2b java_file");
		System.out.println(" If only one file is given on command line,");
		System.out.println(" this file is parsed and the corresponding B");
		System.out.println(" machine is printed to stdout");
		System.out.println(" Otherwise, the n-1 first parameters correspond");
		System.out.println(" to java source files, and the last parameter");
		System.out.println(" correspond to the destination directory where");
		System.out.println(" the generated files are stored");
		System.out.println();
		System.out.println(
			" Properties recognised (java -Dflags jml2b/Jml2b):");
		System.out.println("    -D" + baseFileProperty + "=file_name");
		System.out.println(
			"       Allow using the given file as serialized image of default packages");
		System.out.println("    -D" + jmlPathProperty + "=file_list");
		System.out.println(
			"       Use the given list of directories as Jml search path");
		System.out.println(
			"       The list should contain directories separated by "
				+ java.io.File.pathSeparator);
		System.out.println("    -D" + inFileProperty + "=file");
		System.out.println(
			"       Use the given file as a serialised image of");
		System.out.println("       the parsed files");
		System.out.println(
			"       In this case, a parameter can be given on the");
		System.out.println(
			"       command line corresponding to the destination");
		System.out.println("       directory");
		System.out.println("    -D" + outFileProperty + "=file");
		System.out.println(
			"       Save the parsed files as well as the classes they references");
		System.out.println("       to file.");
		System.out.println("    -D" + propertyFileProperty + "=file");
		System.out.println(
			"        use file as file containing the different properties");
	}

	/** 
	 * Loads files from args.
	 * @param config The current configuration
	 * @param args the file name of the files.
	 **/
	public static JmlFile[] loadFiles(
		IJml2bConfiguration config,
		String[] args) {
		return loadFiles(config, args, args.length);
	}

	/** 
	 * Loads the file_count files from args.
	 * @param config The current configuration
	 * @param file_count the number of files to load.
	 * @param args the file name of the files. This array must contain at
	 * least file_count strings.
	 */
	public static JmlFile[] loadFiles(
		IJml2bConfiguration config,
		String[] args,
		int file_count) {
		// look for a basebin file. This is only done in the case where
		// 
		String base_bin_file = System.getProperty(baseFileProperty);
		if (base_bin_file != null) {
			if (!((JavaLoader) config.getPackage()).initFromFile(base_bin_file)) {
				System.err.println(
					"Unable to initialize from file \"" + base_bin_file + "\"");
				System.exit(1);
			}
		}

		// ensure that the default classes are loaded
		JmlLoader.loadDefaultClasses(config);

		// number of errors that occured when loading the files.
		int error_count = 0;

		// load each of the files
		JmlFile files[] = new JmlFile[file_count];
		for (int i = 0; i < file_count; ++i) {
			try {
				File f = new File(args[i]).getAbsoluteFile();

				if (f.exists()) {
					files[i] = new JmlEntryFile(f).loadFile(config, false);
					if (files[i] == null) {
						System.err.println("Error loading " + f.toString());
						System.exit(1);
					}
				} else {
					System.err.println("File does not exists : " + args[0]);
					System.exit(1);
				}
			} catch (Exception /* IOException */
				e) {
				// gcj requires that IOException been catched in this block
				// whereas javac complains that IOExceptions cannot be
				// thrown within the block
				// => catch Exception instead

				System.err.println(
					"Error loading file " + args[i] + ": " + e.toString());
				System.exit(1);
			}

		}

		// parse each of the loaded files
		for (int i = 0; i < file_count; ++i) {
			error_count += files[i].parse(config);
		}

		// stop if errors where encountered when parsing files
		if (error_count > 0) {
			System.err.println(
				Integer.toString(error_count)
					+ " errors encountered while parsing files");
			System.exit(1);
		}

		// link each of the loaded files
		for (int i = 0; i < file_count; ++i) {
			//	    Debug.print(Debug.LINKING, "Linking : " + args[i] + "...");
			System.err.println("Linking : " + args[i] + "...");
			try {
				files[i].link(config);
			} catch (Jml2bException e) {
				System.err.println("Catched : " + e.toString());
				System.exit(1);
			}
		}

		// link statements from each of the loaded files.
		for (int i = 0; i < file_count; ++i) {
			//Debug.print(Debug.LINKING, "Linking statements: " + args[i] + "...");
			System.err.println("Linking statements: " + args[i] + "...");
			try {
				if (files[i].linkStatements(config) == 0)
					files[i].typeCheck(config);
			} catch (Jml2bException e) {
				System.err.println("Catched : " + e.toString());
				System.exit(1);
			}
		}

		// link statements for all the files that have been automatically 
		// loaded (those files are linked automatically, but their statements
		// are not)
		try {
			JmlLoader.linkStatements(config);
		} catch (Jml2bException e) {
			System.err.println("Catched : " + e.toString());
			System.exit(1);
		}
		return files;
	}

	/**
	 * Saves an image.
	 * @param files The set of Jml file to save
	 * @param file_name The file name of the image
	 **/
	public static void saveFileImage(IJml2bConfiguration config, JmlFile[] files, String file_name)
		throws IOException {
		FileOutputStream str = new FileOutputStream(file_name);
		ObjectOutputStream ostr = new ObjectOutputStream(str);
		// write the packages
		ostr.writeObject(((JavaLoader) config.getPackage()).getRoot());
		// write the JmlFile array
		ostr.writeObject(files);
		ostr.close();
	}

	/**
	 * Restore the JmlFile array as well as the system packages from the given 
	 * file.
	 **/
	public static JmlFile[] loadFileImage(Jml2bConfig config, String file_name) {
		try {
			FileInputStream istr = new FileInputStream(file_name);
			ObjectInputStream ostr = new ObjectInputStream(istr);
			// read packages
			Package root = (Package) ostr.readObject();
			((JavaLoader) config.getPackage()).restoreDefaultPackages(root);
			config.setPackage((JavaLoader) config.getPackage());
			// read file array
			JmlFile[] files = (JmlFile[]) ostr.readObject();

			return files;
		} catch (Exception e) {
			System.err.println("Exception catched : " + e.toString());
			System.exit(1);
			return null;
		}
	}

	/** 
	 * Returns a File object corresponding to the given directory.
	 * create the directory if needed.
	 */
	public static File getOutputDir(String dir_name) {
		File f = new File(dir_name);
		// checks that the directory exists
		if (f.exists()) {
			if (!f.isDirectory()) {
				System.err.println(dir_name + " exists but isn't a directory");
				// if the file exists, but isn't a directory, return null
				f = null;
			}
		} else {
			// create the directory if it does not exists
			if (!f.mkdirs()) {
				System.err.println("Could not create directory: " + dir_name);
				f = null;
			}
		}
		return f;
	}

	private static File getPropertyFile() {
		File result;
		// first, look if a file is given on command line
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

		return null;
	}

	public static void loadProperties() throws IOException {

		File f = getPropertyFile();
		if (f != null) {
			FileInputStream s = new FileInputStream(f);
			Properties props = new Properties(System.getProperties());
			props.load(s);
			s.close();
			System.setProperties(props);
		}
	}

	public static JmlFile[] loadAstImage(
		IJml2bConfiguration config,
		String astFile) {
		int file_count = 0;
		JmlFile files[] = null;
		// look for a basebin file. This is only done in the case where
		// 
		String base_bin_file = System.getProperty(baseFileProperty);
		if (base_bin_file != null) {
			if (!((JavaLoader) config.getPackage()).initFromFile(base_bin_file)) {
				System.err.println(
					"Unable to initialize from file \"" + base_bin_file + "\"");
				System.exit(1);
			}
		}

		// ensure that the default classes are loaded
		JmlLoader.loadDefaultClasses(config);

		// number of errors that occured when loading the files.
		int error_count = 0;

		// load each of the files
		try {
			FileInputStream ostream = new FileInputStream(astFile);
			ObjectInputStream p = new ObjectInputStream(ostream);
			file_count = p.readInt();
			files = new JmlFile[file_count];

			for (int i = 0; i < file_count; ++i) {
				File file_name = new File((String) p.readObject());
				AST a = (LineAST) p.readObject();
				//astprint.tabs = new Tabs();
				//			astprint.walkTree(a, null);
				files[i] = new JmlFile(file_name, a, (JavaLoader) config.getPackage());
			}
			ostream.close();
		} catch (Exception /* IOException */
			e) {
			// gcj requires that IOException been catched in this block
			// whereas javac complains that IOExceptions cannot be
			// thrown within the block
			// => catch Exception instead

			System.err.println(
				"Error loading file "
					+ file_count
					+ " "
					+ astFile
					+ ": "
					+ e.toString());
			System.exit(1);
		}

		// parse each of the loaded files
		for (int i = 0; i < file_count; ++i) {
			error_count += files[i].parse(config);
		}

		// stop if errors where encountered when parsing files
		if (error_count > 0) {
			System.err.println(
				Integer.toString(error_count)
					+ " errors encountered while parsing files");
			System.exit(1);
		}

		// link each of the loaded files
		for (int i = 0; i < file_count; ++i) {
			//	    Debug.print(Debug.LINKING, "Linking : " + args[i] + "...");
			//System.err.println("Linking : " + args[i] + "...");
			try {
				files[i].link(config);
			} catch (Jml2bException e) {
				System.err.println("Catched : " + e.toString());
				System.exit(1);
			}
		}

		// link statements from each of the loaded files.
		for (int i = 0; i < file_count; ++i) {
			//Debug.print(Debug.LINKING, "Linking statements: " + args[i] + "...");
			//System.err.println("Linking statements: " + args[i] + "...");
			try {
				if (files[i].linkStatements(config) == 0)
					files[i].typeCheck(config);
			} catch (Jml2bException e) {
				System.err.println("Catched : " + e.toString());
				System.exit(1);
			}
		}

		// link statements for all the files that have been automatically 
		// loaded (those files are linked automatically, but their statements
		// are not)
		try {
			JmlLoader.linkStatements(config);
		} catch (Jml2bException e) {
			System.err.println("Catched : " + e.toString());
			System.exit(1);
		}

		// set tghe file name from the class name
		//		for (int i = 0; i < file_count; ++i) {
		//			files[i].setFileName(new File("SecProp_ " + i + ".java"));
		//		}

		return files;

	}

	/** 
	 * Parses and converts the given files.  
	 **/
	public static void main(String[] args) {
		File output_directory = null;
		String[] jmlPath = null;
		boolean obviousPo;

		// get the file name that is used for loading properties
		try {
			loadProperties();
		} catch (IOException e) {
			System.err.println("Error loading property file");
		}

		// get the file_in property first, since if it is nonnull, then
		// the app can be launched without arguments
		String file_in = System.getProperty(inFileProperty);

		ErrorHandler.setHandler(new StderrHandler());

		if (file_in == null && args.length < 1) {
			displayUsage();
			System.exit(0);
		}

		// initialize jml search path
		String jml_path_list = System.getProperty(jmlPathProperty);
		if (jml_path_list != null) {
			jmlPath = Util.tokenize(jml_path_list, File.pathSeparator);
		}

		obviousPo = false;
		String obvious_po_string = System.getProperty(obviousPoProperty);
		if (obvious_po_string != null)
			obviousPo = obvious_po_string.equals("true");

		JmlFile[] files;
		Jml2bConfig config = new Jml2bConfig(jmlPath, obviousPo);

		if (file_in != null) {
			// load the files from the given image
			System.err.print("Restoring files from " + file_in + "...");
			files = loadFileImage(config, file_in);
			System.err.println("Done");

			if (args.length > 0) {
				// in this case, the argument should be the destination
				// directory
				output_directory = getOutputDir(args[0]);
				if (output_directory == null) {
					System.exit(1);
				}
			}
		} else {
			// load the files given on the command line.
			// if only one argument is given, then it is the input file.
			// otherwise, the last argument is the destination directory
			if (args.length == 1) {
				System.err.print("Loading " + args[0]);
				files = loadFiles(config, args);
			} else if (args[0].equals("-ast")) {
				System.err.print("Loading ast file...");
				files = loadAstImage(config, args[1]);
				output_directory = getOutputDir(args[args.length - 1]);
				if (output_directory == null) {
					System.exit(1);
				}
			} else {
				System.err.print("Loading files...");
				files = loadFiles(config, args, args.length - 1);
				output_directory = getOutputDir(args[args.length - 1]);
				if (output_directory == null) {
					System.exit(1);
				}
			}
			System.err.println("Done");
		}

		config.setOutputDir(output_directory);

		// dump image if required
		String file_out = System.getProperty(outFileProperty);
		if (file_out != null) {
			try {
				System.err.println("Writing to file: " + file_out);
				saveFileImage(config, files, file_out);
				System.err.println("Done");
			} catch (IOException e) {
				System.err.println("Exception catched: " + e.toString());
			}
		}

		// lemma generation 
		try {
			new Pog().pog(files, config);
		} catch (IOException e) {
			System.err.println(e.toString());
		} catch (PogException e) {
			System.err.println(e.toString());
		} catch (Jml2bException e) {
			System.err.println(e.toString());
		} catch (InternalError e) {
			System.err.println(e.toString());
		}

	}

}
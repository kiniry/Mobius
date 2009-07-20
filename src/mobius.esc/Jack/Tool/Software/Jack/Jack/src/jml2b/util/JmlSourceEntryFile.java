/*
 * Created on Mar 30, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.util;

import jack.util.Logger;

import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Vector;

import jml.ErrorMessage;
import jml.JmlLexer;
import jml.JmlParser;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ClassLoadException;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import antlr.collections.AST;

/**
 * 
 * @author L. Burdy
 */
public abstract class JmlSourceEntryFile extends JmlFileEntry {

		protected abstract InputStream getInputStream() throws IOException ;

	public void loadClass(IJml2bConfiguration config, boolean defaultExternalFile) throws ClassLoadException,
			Jml2bException {
		// load the jml file as an external file
		JmlFile jml = loadFile(config, defaultExternalFile);
		if (jml == null) {
			throw new ClassLoadException("Error reading file: " + getName());
		}

		// parse and link the loaded file
		try {
			jml.parse(config);
		} catch (InternalError ie) {
			ErrorHandler.error(jml, -1, -1, ie.toString());
		}
		jml.link(config);

		// add the file to the list of files remaining
		JmlLoader.unlinkedFiles.push(jml);
	}

	/**
	 * /** Load the given Java/JML file and return a new JmlFile structure
	 */
	public JmlFile loadFile(IJml2bConfiguration config, boolean external) {
		Vector errors = new Vector();
		Vector warnings = new Vector();

		JmlFile result = loadFile(config, external, errors, warnings);

		JmlFile error_file = result;

		// handles the errors and warnings
		if (result == null) {
			// creates a new dummy JmlFile that is only used for displaying
			// errors
			error_file = new JmlFile(toString(), null);
		}

		// handles errors
		Enumeration e = errors.elements();
		while (e.hasMoreElements()) {
			ErrorMessage msg = (ErrorMessage) e.nextElement();
			ErrorHandler.error(error_file, msg.line, msg.column, msg.message);
			result = null;
		}

		// handles warnings
		//LB I supress the display of the warnings coming from the parser
		//		e = warnings.elements();
		//		while (e.hasMoreElements()) {
		//			ErrorMessage msg = (ErrorMessage) e.nextElement();
		//			ErrorHandler.warning(error_file, msg.line, msg.column, msg.message);
		//		}

		return result;
	}
	 /** Load the given Java/JML file and return a new JmlFile structure.
	 * Errors and warnings reported by the JML parser are stored in 
	 * the provided vectors, that contains jml.ErrorMessage.
	 */
	private JmlFile loadFile(
			IJml2bConfiguration config, 
		boolean external,
		Vector error_vector,
		Vector warning_vector) {
		JmlParser parser = null;
		long start = System.currentTimeMillis();

		// initialize the jml parser

		InputStream fs;
		try {
			fs = getInputStream();
		} catch (IOException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		}
		try {
			JmlLexer lexer = new JmlLexer(fs);
			lexer.currentFile = getFile();
			parser = new JmlParser(lexer);
			parser.lexer = lexer;
			parser.errorVector = error_vector;
			parser.warningVector = warning_vector;

			parser.currentFile = getFile();
			parser.errors = 0;
			parser.warnings = 0;
			parser.JML_reading_JML_file = JmlFile.isJmlFile(getName());
			lexer.JML_reading_JML_file = parser.JML_reading_JML_file;
			parser.compilation_unit();
			parser.errors += lexer.errors;
		} catch (antlr.RecognitionException e) {
			try {
				fs.close();
			} catch (IOException ioe) {
				Logger.err.println("Error closing file: " + ioe.toString());

			}
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		} catch (antlr.TokenStreamException e) {
			try {
				fs.close();
			} catch (IOException ioe) {
				Logger.err.println("Error closing file: " + ioe.toString());

			}
			Logger.err.println("Exception catched : " + e.toString());
			return null;
		}

		try {
			fs.close();
		} catch (IOException e) {
			Logger.err.println("Error closing file: " + e.toString());
			return null;
		}

		if (parser == null) {
			return null;
		}
		long end = System.currentTimeMillis();

		// add the time spect in the parser to jmlParserTime
		JmlFile.jmlParserTime += end - start;
		// increase the number of loaded files
		++JmlFile.loadedFilesCount;

		AST tree = parser.getAST();

		return new JmlFile(this, tree, (JavaLoader) config.getPackage(), external);
	}

 
}
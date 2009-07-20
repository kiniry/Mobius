///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: astprint.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b;

import jack.util.Logger;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import jml.JmlLexer;
import jml.JmlParser;
import jml.LineAST;
import jml2b.util.Tabs;
import antlr.collections.AST;

/** 
 * Simple class that prints Java/JML classes.
 * @author A. Requet
 */
public class astprint {
	static Tabs tabs;

	private static String jmlExtensions[] =
		{ ".refines-jml", ".jml", ".jml-refined" };

	private static boolean isJmlFile(String s) {
		for (int i = 0; i < jmlExtensions.length; ++i) {
			if (s.length() > jmlExtensions[i].length()
				&& s.endsWith(jmlExtensions[i])) {
				return true;
			}
		}
		return false;
	}

	static void printNode(AST tree, String[] token_names) {
		int node_type = tree.getType();
		String node_text = tree.getText();

		// affiche le contenu du noeud dans un format lisible (?).
		Logger.get().println(
			tabs.toString()
				+ "| "
				+ token_names[node_type]
				+ " ("
				+ node_type
				+ ") \""
				+ node_text
				+ "\" "
				+ ((LineAST) tree).line
				+ " "
				+ ((LineAST) tree).column);
	}

	static void walkTree(AST tree, String[] token_names) {
		// print the node
		printNode(tree, token_names);

		// if the node has childrens, print its childrens
		AST children = tree.getFirstChild();
		if (children != null) {
			tabs.inc();
			walkTree(children, token_names);
			tabs.dec();
		}

		// if the node has a sibling, print it.
		AST sibling = tree.getNextSibling();
		if (sibling != null) {
			walkTree(sibling, token_names);
		}
	}

	static void checkFile(File f) {
		JmlParser parser = null;

		// initialize the jml parser

		FileInputStream fs;
		try {
			fs = new FileInputStream(f);
		} catch (IOException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return;
		}
		try {
			JmlLexer lexer = new JmlLexer(fs);
			lexer.currentFile = f;
			parser = new JmlParser(lexer);
			parser.lexer = lexer;
			parser.currentFile = f;
			parser.errors = 0;
			parser.warnings = 0;
			parser.JML_reading_JML_file = isJmlFile(f.getName());
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
			return;
		} catch (antlr.TokenStreamException e) {
			try {
				fs.close();
			} catch (IOException ioe) {
				Logger.err.println("Error closing file: " + ioe.toString());

			}
			Logger.err.println("Exception catched : " + e.toString());
			return;
		}

		try {
			fs.close();
		} catch (IOException e) {
			Logger.err.println("Error closing file: " + e.toString());
			return;
		}

		if (parser == null) {
			return;
		}

		AST tree = parser.getAST();

		// r�cup�re la table de conversion token -> chaine de charact�re 
		// correspondante.
		String[] tokens = parser.getTokenNames();

		// maintenant inutile
		tabs = new Tabs();

		//JmlFile file = new JmlFile();
		//file.parse(file_tree);
		walkTree(tree, tokens);
	}

	public static void displayUsage() {
		Logger.get().println("Usage:");
		Logger.get().println(" Jml2b <Java file>");
	}

	public static void main(String[] args) {
		if (args.length < 1) {
			displayUsage();
			System.exit(0);
		}

		try {
			File f = new File(args[0]).getAbsoluteFile();

			if (f.exists()) {
				checkFile(f);
			} else {
				Logger.get().println("File does not exists : " + args[0]);
			}
		} catch (/*IOException */
			Exception e) {
			// gcj requires that IOException been catched in this block
			// whereas javac complains that IOExceptions cannot be
			// thrown within the block
			// => catch Exception instead
		}
	}
}

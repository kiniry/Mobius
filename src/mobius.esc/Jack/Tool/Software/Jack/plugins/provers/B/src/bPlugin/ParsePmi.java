//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ParsePmi.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package bPlugin;

import jack.util.Logger;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import jml2b.util.Tabs;
import pmi.PmiLexer;
import pmi.PmiParser;

import antlr.collections.AST;

/** 
 * @author L. Burdy
 */
public class ParsePmi {
    
	private static Tabs tabs;

	private static void printNode(AST tree, String[] token_names) {
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
				+ "\"");
	}

	private static void walkTree(AST tree, String[] token_names) {
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

	private static void checkFile(File f) {
		PmiParser parser = null;

		// initialize the pmi parser

		FileInputStream fs;
		try {
			fs = new FileInputStream(f);
		} catch (IOException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return;
		}
		try {
			PmiLexer lexer = new PmiLexer(fs);
			lexer.currentFile = f;
			parser = new PmiParser(lexer);
			parser.lexer = lexer;
			parser.currentFile = f;
			parser.errors = 0;
			parser.warnings = 0;
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
		Logger.err.println("Parse OK");

		// r�cup�re la table de conversion token -> chaine de charact�re 
		// correspondante.
		String[] tokens = parser.getTokenNames();

		// maintenant inutile
		tabs = new Tabs();

		walkTree(tree, tokens);
	}

	private static void displayUsage() {
		Logger.get().println("Usage:");
		Logger.get().println(" ParsePmi <Pmi file>");
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

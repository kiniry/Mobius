//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.util;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;

/**
 * @author L. Burdy
 */
public abstract class FileUpdate {

	public static Vector annotateFiles(Vector fileUpdates) throws IOException {
		Vector res = new Vector();
		// Collect the set of files that have to be updated
		Set files = new HashSet();
		Enumeration e = fileUpdates.elements();
		while (e.hasMoreElements()) {
			FileUpdate element = (FileUpdate) e.nextElement();
			files.add(element.getFile());
		}

		Iterator i = files.iterator();
		while (i.hasNext()) {
			File f = (File) i.next();
			// Store, ordered by nine number, the updates to apply to the current
			// file.
			TreeSet ts = new TreeSet(new FileUpdateComparator());
			e = fileUpdates.elements();
			while (e.hasMoreElements()) {
				FileUpdate element = (FileUpdate) e.nextElement();
				if (f == element.getFile())
					ts.add(element);
			}

			// Read the file, line by line.
			Vector lines = new Vector();
			LineNumberReader lnr =
				new LineNumberReader(
					new BufferedReader(
						new InputStreamReader(new FileInputStream(f))));
			while (lnr.ready())
				lines.add(lnr.readLine());
			lnr.close();

			File tmp = File.createTempFile("jack", "java");
			res.add(new UpdatedJmlFile(f, tmp));
			PrintStream os =
				new PrintStream(
					new BufferedOutputStream(new FileOutputStream(tmp)));

			// iterate on each update
			Iterator i1 = ts.iterator();
			e = lines.elements();
			int line = 0;
			while (i1.hasNext()) {
				FileUpdate fu = (FileUpdate) i1.next();
				while (e.hasMoreElements()) {
					String l = (String) e.nextElement();
					if (l.indexOf("//@") != -1 && line == fu.getLine()) {
						// the line contains a single line JML comment and there 
						// is an update at this line.
						// print the line before the comment.
						os.print(l.substring(0, l.indexOf("//@")));
						line++;
						// print the update
						os.println(fu.getString());
						break;
					}
					if (l.indexOf("/*@") != -1) {
						// the line contains the beginning of a JML comment.
						while (l.indexOf("*/") == -1 && line != fu.getLine()) {
							// look for an update in the JML comment.
							// since there is no update, store the current comment
							// in l.
							line++;
							l += "\n" + (String) e.nextElement();
						}
						if (line == fu.getLine()) {
							// an update exists in the JML comment.
							while (l.indexOf("*/") == -1) {
								// Store the end of the comment in l.
								line++;
								l += "\n" + (String) e.nextElement();
							}
							line++;
							// Print the update
							os.print(fu.getString());
							// Print the text after the end of the comment.
							os.println(l.substring(l.indexOf("*/") + 2));
							break;
						} else {
							line++;
							os.println(l);
							continue;
						}
					}
					if (line == fu.getLine()) {
						// the update is not on a JML comment line.
						// Print the update.
						os.println(fu.getString());
						// Print the line.
						os.println(l);
						line++;
						break;
					}
					line++;
					os.println(l);
				}
			}
			while (e.hasMoreElements())
				os.println((String) e.nextElement());
			os.close();
		}
		return res;
	}

	private File f;
	private String s;

	public FileUpdate(File f, String s) {
		this.f = f;
		this.s = s;
	}
	/**
	 * @return
	 */
	public File getFile() {
		return f;
	}

	/**
	 * @return
	 */
	public String getString() {
		return s;
	}
	/**
	 * 
	 */
	public abstract int getLine();

}

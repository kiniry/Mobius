/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id$
 * Author: David R. Cok
 */

package junitutils;
import java.io.PrintStream;
import java.io.*;
import java.util.Iterator;
import java.util.ArrayList;
import java.lang.reflect.Method;

/** This class contains miscellaneous (static) utility functions that are
    useful in writing JUnit functional tests.
*/
public class Utils {

    /** A cached value of the usual System out stream. */
    final private static PrintStream pso = System.out;

    /** A cached value of the usual System err stream. */
    final private static PrintStream pse = System.err;
    
    /** Redirects System.out and System.err to the given PrintStream. 
	Note that setStreams/restoreStreams operate on the global
	values of System.out and System.err; these implementations
	are not synchronized - you will need to take care of any
	race conditions if you utilize these in more than one thread.
    */
    //@ requires ps != null;
    static public void setStreams(PrintStream ps) {
	pso.flush();
	pse.flush();
	System.setOut(ps);
	System.setErr(ps);
    }

    /** Restores System.out and System.err to the initial, 
	system-defined values. It is ok to call this method
	even if setStreams has not been called.
	Note that setStreams/restoreStreams operate on the global
	values of System.out and System.err; these implementations
	are not synchronized - you will need to take care of any
	race conditions if you utilize these in more than one thread.
    */
    static public void restoreStreams() {
	System.setOut(pso);
	System.setErr(pse);
    }

    /** Executes the given command as an external executable, reads the text
	produced and tokenizes it into Strings (separated by whitespace).
	This differs from ExternalInputIterator that simply returns lines.
    */
    //@ requires command != null;
    //@ ensures \result != null;
/*
    static public ArrayList parseResult(String command) throws java.io.IOException {
	Iterator flaglist = new ExternalInputIterator(command);
	ArrayList a = new ArrayList(10); 
	while (flaglist.hasNext()) {
	    java.util.StringTokenizer flags = new java.util.StringTokenizer((String)flaglist.next());
	    while (flags.hasMoreTokens()) { a.add(flags.nextToken()); }
	}
	return a;
    }
*/

    /** Finds the first line with the given String in the given file and parses the content
	into tokens.  Returns an empty array if the String is not present in the file.
    */
    //@ requires content != null && filename != null;
    //@ ensures \result != null;
/*
    static public ArrayList parseFoundLine(String content, String filename) throws java.io.IOException {
	ArrayList a = new ArrayList(10);
	Iterator i = new FileIterator(filename);
	while (i.hasNext()) {
		String s = (String)(i.next());
		if (s.indexOf(content) != -1) {
			QuoteTokenizer f = new QuoteTokenizer(s);
			while (f.hasMoreTokens()) { a.add(f.nextToken()); }
			return a;
		}
	}
	return a;
    }
*/

    /** Parses a string into arguments as if it were a command-line, using
	the QuoteTokenizer to parse the tokens.
    */
    //@ requires s != null;
    //@ ensures \result != null;
    static public String[] parseLine(String s) {
	QuoteTokenizer q = new QuoteTokenizer(s);
	java.util.ArrayList args = new java.util.ArrayList();
	while (q.hasMoreTokens()) {
	    String a = q.nextToken();
	    args.add(a);
	}
	return (String[])args.toArray(new String[args.size()]);
    }
    
    /** An enumerator that parse a string into tokens, according to the
	rules a command-line would use.  White space separates tokens,
	with double-quoted and single-quoted strings recognized.
    */
	// FIXME - does not handle escape sequences in strings, nor 
	// quoted strings that are not the whole token, e.g.
	// a b c+"asd"  should be three tokens, "a", "b", and  c+"asd" .
    static public class QuoteTokenizer {
	String ss;
	char[] cc;
	int pos = 0;
	
	public QuoteTokenizer(String s) {
	    ss = s;
	    cc = s.toCharArray();
	}
	
	public boolean hasMoreTokens() {
	    while (pos < cc.length && Character.isWhitespace(cc[pos])) ++pos;
	    return pos < cc.length;
	}
	
	public String nextToken() {
	    String res = null;
	    while (pos < cc.length && Character.isWhitespace(cc[pos])) ++pos;
	    if (pos == cc.length) return res;
	    int start = pos;
	    if (cc[pos] == '"') {
		++pos;
		while (pos < cc.length && cc[pos] != '"' ) ++pos;
		if (cc[pos] == '"') ++pos;
		res = ss.substring(start+1,pos-1);
	    } else if (cc[pos] == '\'') {
		++pos;
		while (pos < cc.length && cc[pos] != '\'' ) ++pos;
		if (cc[pos] == '\'') ++pos;
		res = ss.substring(start+1,pos-1);
	    } else {
		while (pos < cc.length && !Character.isWhitespace(cc[pos])) ++pos;
		res = ss.substring(start,pos);
	    }
	    return res;
	}
    }
	
    /** Deletes the contents of a directory, including subdirectories.  
	If the second argument is true, the directory itself is deleted as well.
    */
    static public boolean recursivelyRemoveDirectory(File d, 
					boolean removeDirectoryItself) {
	if (!d.exists()) return true;
        boolean success = true;
	File[] fl = d.listFiles();
	if (fl != null) {
	    for (int ff=0; ff<fl.length; ++ff) {
		if (fl[ff].isDirectory()) {
		    if (!recursivelyRemoveDirectory(fl[ff],true)) 
				success = false;
		} else {
		    if (!fl[ff].delete()) success = false;
		}
	    }
	}
	if (removeDirectoryItself) {
	    if (!d.delete()) success = false;
	}
	return success;
    }

    /** Reads the contents of the file with the given name, returning a String.
	This is an optimized version that uses the byte array provided and 
	presumes that the file is shorter than the length of the array.
    */
// FIXME - can we check that the file is too long without losing the efficiency benefits?
    static public String readFile(String filename, byte[] cb) 
					throws java.io.IOException {
	int i = 0;
	int j = 0;
	java.io.FileInputStream f = new java.io.FileInputStream(filename);
	while (j != -1) {
	    i = i + j;
	    j = f.read(cb,i,cb.length-i);
	}
	f.close();
	return new String(cb,0,i);
    }
    
    static public String readFileX(String filename) {
	try {
		return readFile(filename);
	} catch (Exception e ) {
		System.out.println("Could not read file " + filename);
	}
	return null;
    }
    /** Reads the contents of the file with the given name, returning a String. 
	This version presumes the file is shorter than an internal buffer.
FIXME
    */
    static public String readFile(String filename) throws java.io.IOException {
	StringBuffer sb = new StringBuffer(10000);
	char[] cb = new char[10000];
	int j = 0;
	java.io.FileReader f = new java.io.FileReader(filename);
	while (j != -1) {
	    j = f.read(cb,0,cb.length);
	    if (j != -1) sb.append(cb,0,j);
	}
	f.close();
	return sb.toString();
    }
    
    static public String executeCompile(Class cls, String[] args) {
	return executeMethod(cls,"compile",args);
    }

    /** Finds and executes the method with the given name in the given class;
	the method must have a single argument of type String[].  The 'args'
	parameter is supplied to it as its argument.
    */
    static public String executeMethod(Class cls, String methodname, String[] args) {
	try {
            Method method = cls.getMethod(methodname, new Class[] { String[].class });
            return executeMethod(method,args);
        } catch (NoSuchMethodException e) {
	    Utils.restoreStreams();
	    System.out.println("No method compile in class " + cls);
	    e.printStackTrace();
            throw new RuntimeException(e.toString());
        }
    }

    /** Calls the given method on the given String[] argument.  Any standard
	output and error output is collected and returned as the String 
	return value.
    */
    static public String executeMethod(Method method, String[] args) {
	try {
	    ByteArrayOutputStream ba = new ByteArrayOutputStream(10000);
	    PrintStream ps = new PrintStream(ba);
	    Utils.setStreams(ps);
	    boolean b = ((Boolean)(method.invoke(null,new Object[]{args}))).booleanValue();
	    ps.close(); 
	    String s = ba.toString();
	    return s;
	} catch (Exception e) {
	    Utils.restoreStreams();
	    System.out.println(e.toString());
	} finally {
	    Utils.restoreStreams();
        }
	return null;
    }

    static final String ORACLE_SUFFIX = "-expected";
    static final String SAVED_SUFFIX = "-ckd";

    /** Compares the given string to the content of the given file using
	a comparator that ignores platform differences in line-endings.
	The method has the side effect of saving the string value in a file
	for later comparison if the string and file are different, and making
	sure that the actual output file (the -ckd file) is deleted if the
	string and file are the same.
    */
    static public Diff compareStringToFile(String s, String rootname) 
			throws java.io.IOException {
	String ss = Utils.readFile(rootname+ORACLE_SUFFIX);
	Diff df = new Diff( "expected", ss, "actual", s );

	if (!df.areDifferent()) {
	    // If the two strings match, the test succeeds and we make sure
            // that there is no -ckd file to confuse anyone.
	    (new File(rootname+SAVED_SUFFIX)).delete();
	} else {
	    // If the strings do not match, we save the actual string and 
            // fail the test.
	    FileWriter f = new FileWriter(rootname+SAVED_SUFFIX);
	    f.write(s);
	    f.close();
	}
	return df;
    }

    /** This deletes all files (in the current directory) whose
	names match the given pattern in a regular-expression sense;
	however, it is only implemented for patterns consisting of
	characters and at most one '*', since I'm not going to rewrite
	an RE library.
    */
    static public void removeFiles(String pattern) {
	File[] list;
	int k = pattern.indexOf("*");
	if (k == -1) {
		list = new File[] { new File(pattern) };
	} else if (k == 0) {
		final String s = pattern.substring(1);
		FileFilter ff = new FileFilter() { 
			public boolean accept(File f) { return f.isFile() && f.getName().endsWith(s); }
		};
		list = (new File(".")).listFiles(ff);
	} else if (k+1 == pattern.length()) {
		final String s = pattern.substring(0,k);
		FileFilter ff = new FileFilter() { 
                        public boolean accept(File f) { return f.isFile() && f.getName().endsWith(s); }
                };
                list = (new File(".")).listFiles(ff);        
	} else {
		final String s = pattern.substring(0,k);
		final String ss = pattern.substring(k+1);
		final int j = pattern.length()-1;
		FileFilter ff = new FileFilter() { 
                        public boolean accept(File f) { 
				return  f.isFile() && 
				        f.getName().length() >= j && 
					f.getName().startsWith(s) && 
					f.getName().endsWith(ss); }
                };
                list = (new File(".")).listFiles(ff);        
	}

	for (int i = 0; i<list.length; ++i) {
		//System.out.println("DELETING " +list[i].getName());
		list[i].delete();
	}
		
    }
}

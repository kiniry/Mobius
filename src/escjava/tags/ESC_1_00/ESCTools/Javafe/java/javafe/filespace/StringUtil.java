/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.filespace;


/** Misc. utility functions on Strings */

public final class StringUtil {

    /** Remove leading and trailing whitespace (just spaces for now): */
    //@ requires s!=null
    public static String trim_whitespace(String s) {
	while (s.length()>0 && s.charAt(0)==' ')
	    s = s.substring(1,s.length());

	while (s.length()>0 && s.charAt(s.length()-1)==' ')
	    s = s.substring(0,s.length()-1);

	return s;
    }

	
    /** Count the number of times a given character occurs in a String: */
    //@ requires s!=null
    //@ ensures \result>=0
    public static int countChar(String s, char c) {
	int count = 0;
	int start = 0;

	while ((start = s.indexOf(c, start)+1) != 0)
	    count++;

	return count;
    }


    /**
     ** Print an array of Strings on System.out, one string per
     ** line.  Prints "<null>" if list is null.
     **/
    //@ requires list!=null
    public static void printList(String[] list) {
	if (list == null) {
	    System.out.println("<null>");
	    return;
	}
	
	for (int i=0; i<list.length; i++) 
	    System.out.println(list[i]);
    }


    /**
     ** Parse a (possibly empty) separator-separated list into an array of
     **	Strings:
     **/
    //@ ensures \nonnullelements(\result)
    public static String[] parseList(/*@non_null*/ String s, char separator) {
	// Handle empty list case:
	if (s.equals(""))
	    return new String[0];

	int items = countChar(s, separator)+1;
	String[] list = new String[items];

	int start = 0;
	//@ loop_invariant (\forall int j; 0<=j && j<i ==> list[j]!=null);
	for (int i = 0; i < items-1 ; i++) {

	    int nextSep = s.indexOf(separator, start);
	    //@ assume nextSep != -1;
	    list[i] = s.substring(start, nextSep);
	    start = nextSep + 1;
	}

	list[items-1] = s.substring(start);

	return list;
    }


    /** A simple test driver */
    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
	if (args.length != 1) {
	    System.out.println("StringUtil: usage: <cmd> <teststring>");
	    return;
	}
 	System.out.println("Testing using '" + args[0] + "':");
	System.out.println();

	// Test trim_whitespace:
 	System.out.println("Removing whitespace yields '" +
		trim_whitespace(args[0])+ "'");
	System.out.println();

	// Test countChar:
 	System.out.println("# of commas occuring = " +
	    countChar(args[0], ','));
	System.out.println();

	// Test countChar:
 	System.out.println("List elements are: ");
	printList(parseList(args[0], ','));
	System.out.println("(EOL)");
    }
}

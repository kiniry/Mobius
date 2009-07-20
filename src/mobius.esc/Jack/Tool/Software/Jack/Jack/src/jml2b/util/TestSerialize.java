///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: TestSerialize.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.util;

import jack.util.Logger;

import java.io.FileInputStream;
import java.io.ObjectInputStream;

import jml2b.structure.java.Package;

/**
 * @author A. Requet
 */
public class TestSerialize extends Profiler 
{
    public static void displayUsage()
    {

    }

    public static void main(String [] argv)
    {
	if(argv.length < 1) {
	    displayUsage();
	    System.exit(0);
	}
	long start_time = 0;
	long end_time = 0;
	
	Package p = null;

	String base_file = System.getProperty("jml2b.basefile");
	if(base_file != null) {
	    Logger.get().println("Restoring from : " + base_file);
	} else {
	    Logger.get().println("Using file given on command line");
	}

	try {
	    start_time = System.currentTimeMillis();
	    FileInputStream s = new FileInputStream(argv[0]);
	    ObjectInputStream ostream = new ObjectInputStream(s);
	    p = (Package)ostream.readObject();
	    end_time = System.currentTimeMillis();
	} catch(Exception e) {
	    Logger.err.println("Exception catched:");
	    Logger.err.println(e.toString());
	} 
	Logger.get().println("Classes loaded : " + p.getClassCount(true));
	Logger.get().println("Loading time : " + (end_time - start_time));
    }
}

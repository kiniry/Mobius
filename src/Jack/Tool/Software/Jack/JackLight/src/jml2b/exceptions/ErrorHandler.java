///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ErrorHandler.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jml2b.structure.java.JmlFile;
import jml2b.util.Profiler;

/**
 * Interface defining how errors are reported to the user.
 * 
 * @author A. Requet
 */
public abstract class ErrorHandler extends Profiler {
    static int errorCount = 0;
    static int warningCount = 0;

    /**
     * Method that is called in case of error. It should display the error in
     * the appropriate format.
     * 
     * Note that f can be null.
     */
    protected abstract void handleError(
        JmlFile f,
        int line,
        int column,
        String description);

    /** 
     * Method that is called in case of error. It should display the error in
     * the appropriate format.
     * 
     * Note that f can be null.
     */
    protected abstract void handleWarning(
        JmlFile f,
        int line,
        int column,
        String description);

    /**
     * Indicate an error in the specified file, line and column.
     * 
     * This method maintains the error count and delegates the real error 
     * handling to the currently installed handler (if any).
     */
    /*@
      @ modifies errorCount;
      @*/
    public static void error(
        JmlFile f,
        int line,
        int column,
        String description) {
        ++errorCount;
        if (handler != null) {
            handler.handleError(f, line, column, description);
        }
    }

    /**
     * Indicates an error in the specified file, line and column.
     * 
     * This method maintains the warning count and delegates the real error handling
     * to the currently installed handler (if any).
     */
    /*@
      @ modifies warningCount;
      @*/
    public static void warning(
        JmlFile f,
        int line,
        int column,
        String description) {
        ++warningCount;
        if (handler != null) {
            handler.handleWarning(f, line, column, description);
        }
    }

    /** 
     * Reset the error and warnig counters.
     */
    /*@
      @ modifies errorCount, warningCount;
      @*/
    public static void reset() {
        errorCount = 0;
        warningCount = 0;
    }

    /**
     * Return the current error count.
     */
    public static int getErrorCount() {
        return errorCount;
    }

    /**
     * Return the current warning count.
     */
    public static int getWarningCount() {
        return warningCount;
    }

    /** 
     * Set the error handler that should be used.
     */
    /*@
      @ modifies handler;
      @*/
    public static void setHandler(ErrorHandler h) {
        handler = h;
    }

    /** 
     * The actual error handler. 
     * The default handler correspond to a StderrHandler @see StderrHandler
     */
    private /*@ spec_public */ static ErrorHandler handler;
}

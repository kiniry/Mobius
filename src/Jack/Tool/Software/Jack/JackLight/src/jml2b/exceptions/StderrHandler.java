///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: StderrHandler.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jack.util.Logger;
import jml2b.structure.java.JmlFile;

/**
 * A simple error handler that displays errors on stderr in the style of gcc:
 * filename:line:message
 * 
 * @author A. Requet 
 */
public class StderrHandler extends ErrorHandler {
    /**
     * Displays the error using the following format:
     * <pre>filename:line:description</pre>
     * The column parameter is ignored. 
     * 
     * @see ErrorHandler#handleError(JmlFile, int, int, String)
     */
    protected void handleError(
        JmlFile f,
        int line,
        int column,
        String description) {
        if (f != null) {
            Logger.err.println(f.fileName + ":" + line + ":" + description);
        } else {
            Logger.err.print(description);
            if (line >= 0) {
                Logger.err.print(" (line " + line + ")");
            }
            Logger.err.println();
        }
    }

    /**
  	 * Displays the warning on stderr using the following format:
     * <pre>filename:line:description</pre>
     * The column parameter is ignored. 
     * 
     * @see ErrorHandler#handleWarning(JmlFile, int, int, String)
     */
    protected void handleWarning(
        JmlFile f,
        int line,
        int column,
        String description) {
        if (f != null) {
            Logger.err.println(
                "" + f.fileName + ": warning:" + line + ":" + description);
        } else {
            Logger.err.print(description);
            if (line >= 0) {
                Logger.err.print(" (line " + line + ")");
            }
            Logger.err.println();
        }
    }
}

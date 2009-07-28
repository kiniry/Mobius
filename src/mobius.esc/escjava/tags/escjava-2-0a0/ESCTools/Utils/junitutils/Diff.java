/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
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
 */

package junitutils;
import java.util.StringTokenizer;
import java.util.ArrayList;

/**
 * Class for calculating a (somewhat) detailed comparison of two strings.
 *
 * @author Curtis Clifton
 * @version $Revision$
 */

public class Diff {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    /**
     * Calculate a difference between the given strings.
     *
     * @param oldTextLabel a label for the <code>oldText</code> parameter
     * @param oldText a value to be compared
     * @param newTextLabel a label for the <code>newText</code> parameter
     * @param newText a value to be compared
     */
    public Diff( String oldTextLabel, String oldText, 
		 String newTextLabel, String newText ) {
	this.oldText = oldText;
	this.newText = newText;
	calculate(oldTextLabel,newTextLabel);
    }
    
    //---------------------------------------------------------------------
    // OPERATIONS
    //---------------------------------------------------------------------

    private void calculate(String oldTextLabel, String newTextLabel) {
	// Accumulate the diff in resultSB
	StringBuffer resultSB = new StringBuffer( newText.length() );

	String[] oldTextLines = splitByLine( oldText );
	String[] newTextLines = splitByLine( newText );

	// match by lines
	int oPos=0;
	int nPos=0;
	while (oPos<oldTextLines.length && nPos<newTextLines.length) {
	    // this is a pretty dumb algorithm that doesn't handle
	    // things like the insertion of a single new line in one
	    // string or grouping
	    if (!oldTextLines[oPos].equals(newTextLines[nPos])) {
		resultSB.append( (oPos + 1) + OLD_CH + 
				 oldTextLines[oPos] + NEWLINE );
		resultSB.append( (nPos + 1) + NEW_CH + 
				 newTextLines[nPos] + NEWLINE );
		resultSB.append( NEWLINE );
	    } // end of if 
	    oPos++;
	    nPos++;
	}
	// If we reached the end of one array before the other, then this
	// will print the remainders.
	for (;oPos<oldTextLines.length;oPos++) {
	    resultSB.append( (oPos + 1) + OLD_CH + 
			     oldTextLines[oPos] + NEWLINE  );
	} // end of for ()
	for (;nPos<newTextLines.length;nPos++) {
	    resultSB.append( (nPos + 1) + NEW_CH + 
			     newTextLines[nPos] + NEWLINE  );
	} // end of for ()
	
	if (resultSB.length() > 0) {
	    // Some diffs accumulated, so the strings are different
	    areDifferent = true;

	    // Prepend a key to the the results.
	    result = NEWLINE +
		OLD_CH + oldTextLabel + NEWLINE +
		NEW_CH + newTextLabel + NEWLINE +
		NEWLINE +
		resultSB.toString();
	} else {
	    // No diffs accumulated, so the strings must be the same
	    areDifferent = false;
	    result = "";
	}
    }

    private String[] splitByLine( String text ) {
	// thanks to Windows ridiculous two character newlines it is
	// hard to detect blank lines, so we don't bother trying
	StringTokenizer toker = new StringTokenizer( text, DELIM, false );
	ArrayList lines = new ArrayList( oldText.length() / 60 );
	while (toker.hasMoreTokens()) {
	    String tok = toker.nextToken();
	    lines.add(tok);
	}
	String[] result = new String[lines.size()];
	lines.toArray(result);
	return result;
    }

    /**
     * Returns true if strings on which this was constructed are different.
     */
    public /*+@ pure @+*/ boolean areDifferent() {
	return areDifferent;
    }

    /**
     * Returns the differences between the given strings.
     *
     * <pre><jml>
     * ensures !areDifferent() <==> \result.equals( "" );
     * </jml></pre>
     *
     */
    public String result() {
	return result;
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private String oldText;
    private String newText;
    private boolean areDifferent;
    private String result;

    private static final String DELIM = "\n\r\f";
    private static final String NEWLINE = 
	System.getProperty( "line.separator" );
    private static final String OLD_CH = "< ";
    private static final String NEW_CH = "> ";
}

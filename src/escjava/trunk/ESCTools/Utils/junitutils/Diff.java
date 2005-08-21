/*
 * Copyright (C) 2000-2001 Iowa State University
 * 
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
 * 
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2 of the License, or (at your option) any later
 * version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA
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
  //@ requires oldTextLabel != null;
  //@ requires oldText != null;
  //@ requires newTextLabel != null;
  //@ requires newText != null;
  public Diff(String oldTextLabel, String oldText, String newTextLabel,
      String newText) {
    this.oldText = oldText;
    this.newText = newText;
    calculate(oldTextLabel, newTextLabel);
  }

  //---------------------------------------------------------------------
  // OPERATIONS
  //---------------------------------------------------------------------

  /**
   * Sets the values of areDifferent and result according to a comparison
   * between oldText and newText
   * 
   * @param oldTextLabel a label for the <code>oldText</code> parameter
   * @param newTextLabel a label for the <code>newText</code> parameter
   */
  //@ requires oldTextLabel != null;
  //@ requires newTextLabel != null;
  private void calculate(String oldTextLabel, String newTextLabel) {
    // Accumulate the diff in resultSB
    StringBuffer resultSB = new StringBuffer(newText.length());

    String[] oldTextLines = splitByLine(oldText);
    String[] newTextLines = splitByLine(newText);

    // match by lines
    int oPos = 0;
    int nPos = 0;
    int lastOldMatch = -1;
    int lastNewMatch = -1;
    if (oldTextLines.length > 0 && newTextLines.length > 0)
     while (oPos < oldTextLines.length || nPos < newTextLines.length) {
      // this is a pretty dumb algorithm that doesn't handle
      // things like the insertion of a single new line in one
      // string or grouping
      if (oPos >= oldTextLines.length) oPos = oldTextLines.length-1;
      if (nPos >= newTextLines.length) nPos = newTextLines.length-1;
      boolean matched = false;
      for (int i = lastOldMatch+1; i<=oPos; ++i) {
        if (oldTextLines[i].equals(newTextLines[nPos])) {
          // Got a match
          for (int j=lastOldMatch+1; j<i; ++j)
            resultSB.append((j+1) + OLD_CH + oldTextLines[j] + NEWLINE);
          for (int j=lastNewMatch+1; j<nPos; ++j)
            resultSB.append((j+1) + NEW_CH + newTextLines[j] + NEWLINE);
          lastOldMatch = i;
          lastNewMatch = nPos;
          oPos = i+1;
          nPos++;
          matched = true;
          break;
        }
      }
      if (matched) continue;
      for (int i = lastNewMatch+1; i<=nPos; ++i) {
        if (newTextLines[i].equals(oldTextLines[oPos])) {
          // Got a match
          for (int j=lastOldMatch+1; j<oPos; ++j)
            resultSB.append((j+1) + OLD_CH + oldTextLines[j] + NEWLINE);
          for (int j=lastNewMatch+1; j<i; ++j)
            resultSB.append((j+1) + NEW_CH + newTextLines[j] + NEWLINE);
          lastOldMatch = oPos;
          lastNewMatch = i;
          oPos++;
          nPos = i + 1;
          matched = true;
          break;        }
      }
      if (matched) continue;
      oPos++;
      nPos++;
    }
    // If we reached the end of one array before the other, then this
    // will print the remainders.
    for (oPos=lastOldMatch+1; oPos < oldTextLines.length; oPos++) {
      resultSB.append((oPos + 1) + OLD_CH + oldTextLines[oPos] + NEWLINE);
    } // end of for ()
    for (nPos=lastNewMatch+1; nPos < newTextLines.length; nPos++) {
      resultSB.append((nPos + 1) + NEW_CH + newTextLines[nPos] + NEWLINE);
    } // end of for ()

    if (resultSB.length() > 0) {
      // Some diffs accumulated, so the strings are different
      areDifferent = true;

      // Prepend a key to the results.
      result = NEWLINE + OLD_CH + oldTextLabel + NEWLINE + NEW_CH
          + newTextLabel + NEWLINE + NEWLINE + resultSB.toString();
    } else {
      // No diffs accumulated, so the strings must be the same
      areDifferent = false;
      result = "";
    }
  }

  //@ requires text != null;
  //@ ensures \result != null;
  //@ ensures \nonnullelements(\result);
  private String[] splitByLine(String text) {
    // thanks to Windows ridiculous two character newlines it is
    // hard to detect blank lines, so we don't bother trying
    StringTokenizer toker = new StringTokenizer(text, DELIM, false);
    ArrayList lines = new ArrayList(oldText.length() / 60);
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
  //@ private behavior
  //@ ensures \result == areDifferent;
  public /*@ pure @*/ boolean areDifferent() {
    return areDifferent;
  }

  /**
   * Returns the differences between the given strings.
   *  
   */
  //@ private normal_behavior
  //@ ensures \result == result;
  //@ pure
  public String result() {
    return result;
  }

  //---------------------------------------------------------------------
  // PRIVILEGED DATA
  //---------------------------------------------------------------------

  /** This is the supplied old text, to be compared against the new text */
  //@ non_null
  private String oldText;

  /** This is the supplied new text, to be compared against the old text */
  //@ non_null
  private String newText;

  /** This is set to true if the oldText and newText are not the same */
  private boolean areDifferent = false;

  /**
   * This output String holds the description of the differences between the old
   * and new text.
   */
  //@ non_null
  private String result = "";

  //@ private invariant areDifferent <=!=> result.equals("");

  /** This string holds line delimiters */
  //@ non_null
  private static final String DELIM = "\n\r\f";

  /** This is the system new line character */
  //@ non_null
  private static final String NEWLINE = System.getProperty("line.separator");

  /** This string is used to mark lines of old text */
  //@ non_null
  private static final String OLD_CH = "< ";

  /** This string is used to mark lines of new text */
  //@ non_null
  private static final String NEW_CH = "> ";
}

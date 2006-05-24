//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.contentmergeviewer.ITokenComparator;
import org.eclipse.compare.contentmergeviewer.TextMergeViewer;
import org.eclipse.compare.rangedifferencer.IRangeComparator;
import org.eclipse.jdt.core.ToolFactory;
import org.eclipse.jdt.core.compiler.IScanner;
import org.eclipse.jdt.core.compiler.ITerminalSymbols;
import org.eclipse.jdt.core.compiler.InvalidInputException;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration;
import org.eclipse.jdt.ui.text.JavaTextTools;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.custom.ViewForm;

/**
 * A text merge viewer for JML files.
 * 
 * @author L. Burdy
 **/
public class JmlMergeViewer extends TextMergeViewer {

	public JmlMergeViewer(
		ViewForm treeForm,
		CompareConfiguration configuration) {
		super(treeForm, configuration);
	}

	protected ITokenComparator createTokenComparator(String s) {
		return new JavaTokenComparator(s, true);
	}

	protected void configureTextViewer(TextViewer textViewer) {
		if (textViewer instanceof SourceViewer) {
			JavaTextTools jtt = new JavaTextTools(PreferenceConstants.getPreferenceStore());
			((SourceViewer) textViewer).configure(
				new JavaSourceViewerConfiguration(
					jtt.getColorManager(),
					PreferenceConstants.getPreferenceStore(),
					null,
					null));
		}
	}
	
	
	
	 /**
	  * A comparator for Java tokens.
	  */
	 public class JavaTokenComparator implements ITokenComparator {
	 		
	 	private String fText;
	 	private boolean fShouldEscape= true;
	 	private int fCount;
	 	private int[] fStarts;
	 	private int[] fLengths;

	 	/**
	 	 * Creates a TokenComparator for the given string.
	 	 */
	 	public JavaTokenComparator(String text, boolean shouldEscape) {
	 		
	 		
	 		fText= text;
	 		fShouldEscape= shouldEscape;
	 		
	 		int length= fText.length();
	 		fStarts= new int[length];
	 		fLengths= new int[length];
	 		fCount= 0;
	 		
	 		IScanner scanner= ToolFactory.createScanner(true, true, false, false); // returns comments & whitespace
	 		scanner.setSource(fText.toCharArray());
	 		try {
	 			int endPos= 0;
	 			while (scanner.getNextToken() != ITerminalSymbols.TokenNameEOF) {
	 				int start= scanner.getCurrentTokenStartPosition();
	 				int end= scanner.getCurrentTokenEndPosition()+1;
	 				fStarts[fCount]= start;
	 				fLengths[fCount]= end - start;
	 				endPos= end;
	 				fCount++;
	 			}
	 			// workaround for #13907
	 			if (endPos < length) {
	 				fStarts[fCount]= endPos;
	 				fLengths[fCount]= length-endPos;
	 				fCount++;
	 			}
	 		} catch (InvalidInputException ex) {
	 			// NeedWork
	 		}
	 	}	

	 	/**
	 	 * Returns the number of token in the string.
	 	 *
	 	 * @return number of token in the string
	 	 */
	 	public int getRangeCount() {
	 		return fCount;
	 	}

	 	/* (non Javadoc)
	 	 * see ITokenComparator.getTokenStart
	 	 */
	 	public int getTokenStart(int index) {
	 		if (index >= 0 && index < fCount)
	 			return fStarts[index];
	 		if (fCount > 0)
	 			return fStarts[fCount-1] + fLengths[fCount-1];
	 		return 0;
	 	}

	 	/* (non Javadoc)
	 	 * see ITokenComparator.getTokenLength
	 	 */
	 	public int getTokenLength(int index) {
	 		if (index < fCount)
	 			return fLengths[index];
	 		return 0;
	 	}
	 	
	 	/**
	 	 * Returns <code>true</code> if a token given by the first index
	 	 * matches a token specified by the other <code>IRangeComparator</code> and index.
	 	 *
	 	 * @param thisIndex	the number of the token within this range comparator
	 	 * @param other the range comparator to compare this with
	 	 * @param otherIndex the number of the token within the other comparator
	 	 * @return <code>true</code> if the token are equal
	 	 */
	 	public boolean rangesEqual(int thisIndex, IRangeComparator other, int otherIndex) {
	 		if (other != null && getClass() == other.getClass()) {
	 			JavaTokenComparator tc= (JavaTokenComparator) other;	// safe cast
	 			int thisLen= getTokenLength(thisIndex);
	 			int otherLen= tc.getTokenLength(otherIndex);
	 			if (thisLen == otherLen)
	 				return fText.regionMatches(false, getTokenStart(thisIndex), tc.fText, tc.getTokenStart(otherIndex), thisLen);
	 		}
	 		return false;
	 	}

	 	/**
	 	 * Aborts the comparison if the number of tokens is too large.
	 	 *
	 	 * @return <code>true</code> to abort a token comparison
	 	 */
	 	public boolean skipRangeComparison(int length, int max, IRangeComparator other) {

	 		if (!fShouldEscape)
	 			return false;

	 		if (getRangeCount() < 50 || other.getRangeCount() < 50)
	 			return false;

	 		if (max < 100)
	 			return false;

	 		if (length < 100)
	 			return false;

	 		if (max > 800)
	 			return true;

	 		if (length < max / 4)
	 			return false;

	 		return true;
	 	}
	 }
}

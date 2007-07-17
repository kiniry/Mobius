/*******************************************************************************
 * Copyright (c) 2004 Coffee-Bytes.com and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Common Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.opensource.org/licenses/cpl.php
 * 
 * Contributors:
 *     Coffee-Bytes.com - initial API and implementation
 *******************************************************************************/
package com.cb.eclipse.folding.java.calculation;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.IJavaElement;
// @phosphorus
import org.eclipse.jdt.core.ISourceReference;
// end @phosphorus
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.ITerminalSymbols;

import com.cb.eclipse.folding.EnhancedPosition;
import com.cb.eclipse.folding.java.JavaPositionMetadata;

/**
 * The CommentHelper class is just a common location for the core logic of
 * processing comments and producing comment folding regions.
 * 
 * One of the key components of the comment helper class is the comment folding
 * advisor, which is the client provided class the provides the knowledge of
 * whether certain regions should be foldable and/or collapsed initially.
 * Because the comment helper class is generic in nature, the advisor allows for
 * pluggable scenarios.
 * 
 * @author R.J. Lorimer
 */
public class CommentHelper {

	private Set regions = new HashSet();

	private int lineCommentCount;

	private int lineCommentStart;

	private int lineCommentEnd;
	
	// @phosphorus
	private int lineJMLCount;
	private int lineJMLStart;
	private int lineJMLEnd;
	// end @phosphorus
	
	private CommentFoldingAdvisor advisor;
	private UserDefinedRegionHelper userDefinedRecognizer;

	public CommentHelper() {
		this(DefaultCommentFoldingAdvisor.getInstance());
	}

	public CommentHelper(CommentFoldingAdvisor advisor) {
		this.advisor = advisor;
		userDefinedRecognizer = new UserDefinedRegionHelper();
	}

	public void handle(int token, int start, int end, IJavaElement owner) throws JavaModelException {
		// @phosphorus
		ISourceReference source = (ISourceReference) owner;
		int offset = source.getSourceRange().getOffset();
		boolean isJML = false;
		String possible_at_character;
		// end @phosphorus
		
		switch(token) {
			
			case ITerminalSymbols.TokenNameCOMMENT_BLOCK:
				// @phosphorus bugfix (two parts, this is part one):
				/*
				 * Bug: When there are multiple comments (it doesn't
				 * matter whether they are JML annotations or not)
				 * the boundaries of line comment blocks are wrongly
				 * assigned. This can cause overlap of different
				 * foldable regions. To fix this. it is important
				 * to close any open line comment/JML blocks
				 * not only before a non-comment elements
				 * but before block comment/JML elements as well.
				 */
				closeOpenJML();
				closeOpenComments();
				// end @phosphorus
				
				// @phosphorus
				possible_at_character = source.getSource().substring(start-offset+2, start-offset+3);
				isJML = possible_at_character.equalsIgnoreCase("@");
				
				if (isJML) {
					handleJMLBlock(start, end);
				} else {
				// end @phosphorus
					handleCommentBlock(start, end);
				}
				break;
			case ITerminalSymbols.TokenNameCOMMENT_JAVADOC:
				// @phosphorus bugfix (part two, part one is above):
				closeOpenJML();
				closeOpenComments();
				// end @phosphorus
				
				handleJavadoc(start, end);
				break;
			default:
				if(ITerminalSymbols.TokenNameCOMMENT_LINE == token && !isUserDefinedSentinel(token, start, end, owner)) {
					// @phosphorus
					possible_at_character = source.getSource().substring(start-offset+2, start-offset+3);
					isJML = possible_at_character.equalsIgnoreCase("@");

					if (isJML) {
						handleJMLLine(start, end);
					} else {
					// end @phosphorus
						handleCommentLine(start, end);
					}
				}
				else {
					handleNonCommentToken(token);
				}
				break;
		}
	}

	public void end() {
		closeOpenComments();
		closeOpenJML();
	}

	public Set result() {
		return regions;
	}

	public void reset() {
		regions.clear();
	}
	
	private boolean isUserDefinedSentinel(int token, int start, int end, IJavaElement owner) throws JavaModelException {
		return userDefinedRecognizer.isOpeningSentinel(start, end, owner) || userDefinedRecognizer.isClosingSentinel(start, end, owner);
	}

	private void handleCommentLine(int startPos, int endPos) {

		if (lineCommentCount == 0) {
			lineCommentStart = startPos;

		}
		lineCommentEnd = endPos;
		lineCommentCount++;

	}

	private void handleCommentBlock(int start, int end) {

		if (advisor.shouldFoldBlockComment()) {
			boolean collapse = advisor.shouldCollapseBlockComment();
			regions.add(new EnhancedPosition(start, end - start, getMetadata(collapse)));
		}
	}

	private void handleJavadoc(int start, int end) {
		if (advisor.shouldFoldJavadoc()) {
			boolean collapse = advisor.shouldCollapseJavadoc();
			regions.add(new EnhancedPosition(start, end - start, getMetadata(collapse)));
		}
	}
	
	// @phosphorus
	private void handleJMLBlock(int start, int end) {
		if (advisor.shouldFoldBlockJML()) {
			boolean collapse = advisor.shouldCollapseBlockJML();
			regions.add(new EnhancedPosition(start, end - start,
					getMetadata(collapse)));
		}
	}
	
	private void handleJMLLine(int start, int end) {
		if (lineJMLCount == 0) {
			lineJMLStart = start;
		}
		
		lineJMLEnd = end;
		lineJMLCount++;
	}
	// end @phosphorus

	private void handleNonCommentToken(int token) {

		closeOpenComments();
		// @phosphorus
		closeOpenJML();
		// end @phosphorus
	}

	private void closeOpenComments() {
		if (lineCommentCount > 1) {

			if (advisor.shouldFoldLineComment()) {
				boolean collapse = advisor.shouldCollapseLineComment();
				regions.add(new EnhancedPosition(lineCommentStart, lineCommentEnd - lineCommentStart - 1, getMetadata(collapse)));
			}
			
		}
		lineCommentCount = 0;			
	}
	// @phosphorus
	private void closeOpenJML() {
		if (lineJMLCount > 1) {
			if (advisor.shouldFoldLineJML()) {
				boolean collapse = advisor.shouldCollapseLineJML();
				regions.add(new EnhancedPosition(lineJMLStart,
					lineJMLEnd - lineJMLStart - 1, getMetadata(collapse)));
			}
		}
		lineJMLCount = 0;
	}
	// end @phosphorus

	public String toString() {
		return "Comment Helper - regions: " + result().size();
	}

	private JavaPositionMetadata getMetadata(boolean collapse) {
		return new JavaPositionMetadata(false, false, collapse, false, null);
	}
	
}
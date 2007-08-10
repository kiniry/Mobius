/*******************************************************************************
 * Copyright (c) 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

/*
 * phosphorus says: 
 * Taken from org.eclipse.jdt.ui.text.folding.DefaultFoldingStructureProvider.java
 */

package com.grok.fisheye.folding.java;

import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.text.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.projection.IProjectionPosition;

/**
 * Projection position that will return two foldable regions: one folding away
 * the lines before the one containing the simple name of the java element, one
 * folding away any lines after the caption.
 */
public final class JavaElementPosition extends Position implements IProjectionPosition {

	private IMember fMember;

	public JavaElementPosition(int offset, int length, IMember member) {
		super(offset, length);
		Assert.isNotNull(member);
		fMember= member;
	}
	
	public void setMember(IMember member) {
		Assert.isNotNull(member);
		fMember= member;
	}
	
	/*
	 * @see org.eclipse.jface.text.source.projection.IProjectionPosition#computeFoldingRegions(org.eclipse.jface.text.IDocument)
	 */
	public IRegion[] computeProjectionRegions(IDocument document) throws BadLocationException {
		int nameStart= offset;
		try {
			/* The member's name range may not be correct. However,
			 * reconciling would trigger another element delta which would
			 * lead to reentrant situations. Therefore, we optimistically
			 * assume that the name range is correct, but double check the
			 * received lines below. */
			ISourceRange nameRange= fMember.getNameRange();
			if (nameRange != null)
				nameStart= nameRange.getOffset();

		} catch (JavaModelException e) {
			// ignore and use default
		}

		int firstLine= document.getLineOfOffset(offset);
		int captionLine= document.getLineOfOffset(nameStart);
		int lastLine= document.getLineOfOffset(offset + length);

		/* see comment above - adjust the caption line to be inside the
		 * entire folded region, and rely on later element deltas to correct
		 * the name range. */
		if (captionLine < firstLine)
			captionLine= firstLine;
		if (captionLine > lastLine)
			captionLine= lastLine;

		IRegion preRegion;
		if (firstLine < captionLine) {
			int preOffset= document.getLineOffset(firstLine);
			IRegion preEndLineInfo= document.getLineInformation(captionLine);
			int preEnd= preEndLineInfo.getOffset();
			preRegion= new Region(preOffset, preEnd - preOffset);
		} else {
			preRegion= null;
		}

		if (captionLine < lastLine) {
			int postOffset= document.getLineOffset(captionLine + 1);
			IRegion postRegion= new Region(postOffset, offset + length - postOffset);

			if (preRegion == null)
				return new IRegion[] { postRegion };

			return new IRegion[] { preRegion, postRegion };
		}

		if (preRegion != null)
			return new IRegion[] { preRegion };

		return null;
	}

	/*
	 * @see org.eclipse.jface.text.source.projection.IProjectionPosition#computeCaptionOffset(org.eclipse.jface.text.IDocument)
	 */
	public int computeCaptionOffset(IDocument document) throws BadLocationException {
		int nameStart= offset;
		try {
			// need a reconcile here?
			ISourceRange nameRange= fMember.getNameRange();
			if (nameRange != null)
				nameStart= nameRange.getOffset();
		} catch (JavaModelException e) {
			// ignore and use default
		}

		return nameStart - offset;
	}

}

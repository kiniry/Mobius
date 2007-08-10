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

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;

/**
 * A {@link ProjectionAnnotation} for java code.
 */
public final class JavaProjectionAnnotation extends ProjectionAnnotation {

	
	private IJavaElement fJavaElement;
	private boolean fIsComment;
	
	private boolean is_region;
	private boolean is_jml;
	
	private boolean my_changed;

	/**
	 * Creates a new projection annotation.
	 * 
	 * @param isCollapsed <code>true</code> to set the initial state to collapsed,
	 *        <code>false</code> to set it to expanded
	 * @param element the java element this annotation refers to
	 * @param isComment <code>true</code> for a foldable comment, <code>false</code> for a
	 *        foldable code element
	 */
	public JavaProjectionAnnotation(IJavaElement an_element, boolean is_comment, boolean a_region, boolean a_jml) {
		super(false);
		fJavaElement= an_element;
		
		fIsComment= is_comment;
		is_region = a_region;
		is_jml = a_jml;
		
		my_changed = false;
	}
	
	/* @region commands */
	
	protected void setElement(IJavaElement element) {
		fJavaElement= element;
	}
	
	protected void setIsRegion(boolean new_value) {
		is_region = new_value;
	}
	
	protected void setIsJml(boolean new_value) {
		is_jml = new_value;
	}
	
	protected void setIsComment(boolean isComment) {
		fIsComment= isComment;
	}
	
	public void markChanged() {
		my_changed = true;
	}
	
	protected void unmarkChanged() {
		my_changed = false;
	}

	/* @region queries */
	
	public IJavaElement getElement() {
		return fJavaElement;
	}

	public boolean isComment() {
		return fIsComment;
	}
	
	protected boolean isRegion() {
		return is_region;
	}
	
	protected boolean isJml() {
		return is_jml;
	}
	
	protected boolean isMarkedChanged() {
		return my_changed;
	}
	
	public boolean belongsUnder(JavaProjectionAnnotation an_annotation) {
		if (an_annotation == null) {
			return false;
		}
		
		ISourceReference a_source = (ISourceReference)an_annotation.getElement();
		ISourceRange a_range = null;
		
		ISourceReference my_source = (ISourceReference)this.getElement();
		ISourceRange my_range = null;
	
		try {
			 a_range = a_source.getSourceRange();
			 my_range = my_source.getSourceRange();
		} catch (JavaModelException e) {
			// TODO catch?
			e.printStackTrace();
		}
		
		int my_offset = my_range.getOffset();
		int an_offset = a_range.getOffset();
		
		int a_length = a_range.getLength();
		int my_length = my_range.getLength();
		
		if (my_offset >= an_offset && ((my_offset+my_length) <= (an_offset+a_length))) {
			return true;
		} else {
			return false;
		}
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "JavaProjectionAnnotation:\n" + //$NON-NLS-1$
				"\telement: \t"+ fJavaElement.toString() + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
				"\tcollapsed: \t" + isCollapsed() + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
				"\tcomment: \t" + isComment() + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
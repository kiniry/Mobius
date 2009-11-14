/*******************************************************************************
 * Copyright (c) 2000, 2005 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package ie.ucd.bon.plugin.editor;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.plugin.editor.outline.BONOutlinePage;
import ie.ucd.bon.plugin.util.PluginUtil;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.AstUtil;

import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;


/**
 * BON editor.
 */
public class BONEditor extends TextEditor {

	/** The projection support */
	private ProjectionSupport fProjectionSupport;
	
	
	public BONEditor() {
		super();
	}
	
	
	/* (non-Javadoc)
	 * Method declared on AbstractTextEditor
	 */
	protected void initializeEditor() {
		super.initializeEditor();
		setSourceViewerConfiguration(new BONSourceViewerConfiguration());
	}
	
	/*
	 * @see org.eclipse.ui.texteditor.ExtendedTextEditor#createSourceViewer(org.eclipse.swt.widgets.Composite, org.eclipse.jface.text.source.IVerticalRuler, int)
	 */
	protected ISourceViewer createSourceViewer(Composite parent, IVerticalRuler ruler, int styles) {
		
		fAnnotationAccess= createAnnotationAccess();
		fOverviewRuler= createOverviewRuler(getSharedColors());
		
		ISourceViewer viewer= new ProjectionViewer(parent, ruler, getOverviewRuler(), isOverviewRulerVisible(), styles);
		// ensure decoration support has been created and configured.
		getSourceViewerDecorationSupport(viewer);
		return viewer;
	}
	
	/*
	 * @see org.eclipse.ui.texteditor.ExtendedTextEditor#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {
		super.createPartControl(parent);
		ProjectionViewer viewer= (ProjectionViewer) getSourceViewer();
		fProjectionSupport = new ProjectionSupport(viewer, getAnnotationAccess(), getSharedColors());
		fProjectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.error"); //$NON-NLS-1$
		fProjectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.warning"); //$NON-NLS-1$
		fProjectionSupport.install();
		viewer.doOperation(ProjectionViewer.TOGGLE);
	}

	IContentOutlinePage outline = null;
  @Override
  public Object getAdapter(Class adapter) {
    if (IContentOutlinePage.class.equals(adapter)) {
      if (outline == null) {
        outline = new BONOutlinePage(this);
      }
      return outline;
   }
    return super.getAdapter(adapter);
  }
  
  public void selectAndReveal(AstNode node) {
    SourceLocation location = AstUtil.getReportingSourceLocation(node);
    if (location.isRealLocation()) {
      int startChar = PluginUtil.eclipseAbsoluteCharacterPosition(location.getAbsoluteCharPositionStart(), location.getLineNumber());
      int endChar = PluginUtil.eclipseAbsoluteCharacterPosition(location.getAbsoluteCharPositionEnd(), location.getLineNumber());
      this.selectAndReveal(startChar, endChar-startChar+1);
    }
  }
	
}

/**
 * 
 */
package com.grok.fisheye.folding;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.ElementChangedEvent;
import org.eclipse.jdt.core.IElementChangedListener;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaElementDelta;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IParent;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.ToolFactory;
import org.eclipse.jdt.core.compiler.IScanner;
import org.eclipse.jdt.core.compiler.ITerminalSymbols;
import org.eclipse.jdt.core.compiler.InvalidInputException;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.ClassFileEditor;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jdt.internal.ui.javaeditor.IClassFileEditorInput;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;

import org.eclipse.jdt.ui.IWorkingCopyManager;

import org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider;
import org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension;
import org.eclipse.jdt.ui.text.folding.DefaultJavaFoldingStructureProvider.FoldingStructureComputationContext;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.projection.IProjectionListener;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionViewer;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;

import org.eclipse.swt.graphics.Point;

import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import com.grok.fisheye.folding.doi.FisheyeTree;
import com.grok.fisheye.folding.java.JavaProjectionAnnotation;
import com.grok.fisheye.folding.java.CommentPosition;

/**
 * 
 * @author phosphorus
 */
public class FisheyeJavaFoldingStructureProvider implements
IJavaFoldingStructureProvider, IJavaFoldingStructureProviderExtension  {

	private ITextEditor my_editor;
	private IJavaElement my_input;
	private ProjectionViewer my_viewer;
	private ProjectionAnnotationModel my_annotation_model;
	private IDocument my_document;

	private ElementChangedListener my_element_changed_listener;
	private ProjectionListener my_projection_listener;

	private FisheyeTree my_fisheye;

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider#initialize()
	 */
	@Override
	public void initialize() { 
		if (isInstalled()) {
			updateStructure();
			updateAnnotations();
		}

	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider#install(org.eclipse.ui.texteditor.ITextEditor, org.eclipse.jface.text.source.projection.ProjectionViewer)
	 */
	@Override
	public void install(ITextEditor some_editor, ProjectionViewer some_viewer) {
		if (isSupported(some_editor)) {
			my_editor = some_editor;
			my_viewer = some_viewer;

			my_annotation_model = (ProjectionAnnotationModel) my_editor.getAdapter(ProjectionAnnotationModel.class);

			my_document =  getDocument();

			my_element_changed_listener = new ElementChangedListener();
			my_projection_listener = new ProjectionListener();
			my_viewer.addProjectionListener(my_projection_listener);

			my_fisheye = new FisheyeTree();

		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider#uninstall()
	 */
	@Override
	public void uninstall() {
		if (isInstalled()) {
			my_projection_listener.projectionDisabled();

			my_viewer.removeProjectionListener(my_projection_listener);
			my_projection_listener = null;
			my_element_changed_listener = null;

			my_viewer = null;
			my_editor = null;
			my_annotation_model = null;
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseComments()
	 */
	@Override
	public void collapseComments() {
		/* we don't want anyone to touch collapsing except for the fisheye
		 * for quite obvious reasons...
		 */


	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseElements(org.eclipse.jdt.core.IJavaElement[])
	 */
	@Override
	public void collapseElements(IJavaElement[] elements) {
		/* we don't want anyone to touch collapsing except for the fisheye
		 * for quite obvious reasons...
		 */
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseMembers()
	 */
	@Override
	public void collapseMembers() {
		/* we don't want anyone to touch collapsing except for the fisheye
		 * for quite obvious reasons...
		 */
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#expandElements(org.eclipse.jdt.core.IJavaElement[])
	 */
	@Override
	public void expandElements(IJavaElement[] elements) {
		/* we don't want anyone to touch expanding except for the fisheye
		 * for quite obvious reasons...
		 */

	}

	/**
	 * This method checks if the editor that we are working with is a 
	 * <code>JavaEditor</code>.
	 * @param an_editor the editor that we want to check
	 * @return true if the given editor is a JavaEditor, false if not
	 */
	private boolean isSupported(ITextEditor an_editor) {
		return (an_editor instanceof JavaEditor);
	}

	/**
	 * This method checks if the Provider has been installed or not.
	 * @return true if the provider is installed, false if not
	 */
	private boolean isInstalled() {
		return (my_editor != null);
	}

	/* IBM */
	private IDocument getDocument() {
		IDocumentProvider my_document_provider= my_editor.getDocumentProvider();
		return my_document_provider.getDocument(my_editor.getEditorInput());
	}

	/* @region commands */




	/*IBM: DefaultJavaFoldingStructureProvider*/
	private void computeFoldingStructure() {
		IParent parent= (IParent) my_input;
		try {
			computeFoldingStructure(parent.getChildren());
		} catch (JavaModelException x) {
		}
	}
	/*IBM: DefaultJavaFoldingStructureProvider*/
	private void computeFoldingStructure(IJavaElement[] elements) throws JavaModelException {
		for (int i= 0; i < elements.length; i++) {
			IJavaElement element= elements[i];

			computeFoldingStructure(element);

			if (element instanceof IParent) {
				IParent parent= (IParent) element;
				computeFoldingStructure(parent.getChildren());
			}
		}
	}

	/**
	 * Computes the folding structure for a given {@link IJavaElement java element}. Computed
	 * projection annotations are
	 * {@link DefaultJavaFoldingStructureProvider.FoldingStructureComputationContext#addAnnoation(DefaultJavaFoldingStructureProvider.JavaProjectionAnnotation, Position) added}
	 * to the computation context.
	 * <p>
	 * Subclasses may extend or replace. The default implementation creates projection annotations
	 * for the following elements:
	 * <ul>
	 * <li>true members (not for top-level types)</li>
	 * <li>the javadoc comments of any member</li>
	 * <li>header comments (javadoc or multi-line comments appearing before the first type's
	 * javadoc or before the package or import declarations).</li>
	 * </ul>
	 * </p>
	 * 
	 * @param element the java element to compute the folding structure for
	 * @param ctx the computation context
	 */
	/*IBM: DefaultJavaFoldingStructureProvider*/
	protected void computeFoldingStructure(IJavaElement element) {

		boolean collapse= false;
		boolean collapseCode= true;
		// @phosphorus begin unnecessary check
		/* I could use it to distinguish comments though...*/
		switch (element.getElementType()) {

		case IJavaElement.IMPORT_CONTAINER:
			collapse= ctx.collapseImportContainer();
			break;
		case IJavaElement.TYPE:
			collapseCode= isInnerType((IType) element) && !isAnonymousEnum((IType) element);
			collapse= ctx.collapseInnerTypes() && collapseCode;
			break;
		case IJavaElement.METHOD:
		case IJavaElement.FIELD:
		case IJavaElement.INITIALIZER:
			collapse= ctx.collapseMembers();
			break;
		default:
			return;
		}
		// end check

		Position[] my_positions= computeProjectionRangePositions((ISourceReference) element);
		if (my_positions.length > 0) {
			// comments
			for (int i= 0; i < my_positions.length - 1; i++) {
				IRegion normalized= alignRegion(my_positions[i]);
				if (normalized != null) {
					Position my_comment_position= createCommentPosition(normalized);
					if (position != null) {
						// @phosphorus begin unnecessary check
						boolean commentCollapse;
						boolean is_region;
						boolean is_jml;
						if (i == 0 && (my_positions.length > 2 || ctx.hasHeaderComment()) && element == ctx.getFirstType()) {
							//commentCollapse= ctx.collapseHeaderComments();
						} else {
							//commentCollapse= ctx.collapseJavadoc();
						}
						// end check
						my_fisheye.addAnnotation(new JavaProjectionAnnotation(element, true, is_region, is_jml), my_comment_position);
					}
				}
			}
			// code
			/* this should come first to create the parent node first and then attach the comments as children...*/
			if (collapseCode) {
				IRegion normalized= alignRegion(my_positions[my_positions.length - 1]);
				if (normalized != null) {
					Position position= element instanceof IMember ? createMemberPosition(normalized, (IMember) element) : createCommentPosition(normalized);
					if (position != null)
						my_fisheye.addAnnotation(new JavaProjectionAnnotation(element, false, false, false), position);
				}
			}
		}
	}

	/**
	 * Computes the projection ranges for a given <code>ISourceReference</code>. More than one
	 * range or none at all may be returned. If there are no foldable regions, an empty array is
	 * returned.
	 * <p>
	 * The last region in the returned array (if not empty) describes the region for the java
	 * element that implements the source reference. Any preceding regions describe javadoc comments
	 * of that java element.
	 * </p>
	 * 
	 * @param a_reference a java element that is a source reference
	 * @param ctx the folding context
	 * @return the regions to be folded
	 */
	/* IBM, code changed */
	protected final Position[] computeProjectionRangePositions(ISourceReference a_reference) {
		try {

			ISourceRange range= a_reference.getSourceRange();

			String contents= a_reference.getSource();
			if (contents == null)
				return new Position[0];

			List<Position> my_positions= new ArrayList<Position>();
			if (!ctx.hasFirstType() && a_reference instanceof IType) {
				ctx.setFirstType((IType) a_reference);
				IRegion headerComment= computeHeaderComment(ctx);
				if (headerComment != null) {
					//TODO change computeHeaderComment to return Position instead of Region!
					my_positions.add(headerComment);
					ctx.setHasHeaderComment();
				}
			}

			IScanner scanner= ToolFactory.createScanner(true, false, false, false);
			scanner.setSource(contents.toCharArray());
			final int shift= range.getOffset();
			int start= shift;
			while (true) {

				int token= scanner.getNextToken();
				start= shift + scanner.getCurrentTokenStartPosition();

				switch (token) {
				case ITerminalSymbols.TokenNameCOMMENT_JAVADOC:
				case ITerminalSymbols.TokenNameCOMMENT_BLOCK: {
					int end= shift + scanner.getCurrentTokenEndPosition() + 1;
					my_positions.add(new CommentPosition(start, end - start));
				}
				case ITerminalSymbols.TokenNameCOMMENT_LINE:
					continue;
				}

				break;
			}

			Region a_region = new Region(start, shift + range.getLength() - start);
			Region an_aligned_region = (Region)alignRegion(a_region);

			my_positions.add(new Position());

			Position[] result= new Position[my_positions.size()];
			my_positions.toArray(result);
			return result;
		} catch (JavaModelException e) {
		} catch (InvalidInputException e) {
		}

		return new Position[0];
	}

	/**
	 * Aligns <code>region</code> to start and end at a line offset. The region's start is
	 * decreased to the next line offset, and the end offset increased to the next line start or the
	 * end of the document. <code>null</code> is returned if <code>region</code> is
	 * <code>null</code> itself or does not comprise at least one line delimiter, as a single line
	 * cannot be folded.
	 * 
	 * @param a_region the region to align, may be <code>null</code>
	 * @param ctx the folding context
	 * @return a region equal or greater than <code>region</code> that is aligned with line
	 *         offsets, <code>null</code> if the region is too small to be foldable (e.g. covers
	 *         only one line)
	 */
	/* IBM */
	private final IRegion alignRegion(IRegion a_region) {
		if (a_region == null)
			return null;

		try {

			int my_start = my_document.getLineOfOffset(a_region.getOffset());
			int my_end = my_document.getLineOfOffset(a_region.getOffset() + a_region.getLength());
			if (my_start >= my_end)
				return null;

			int my_offset= my_document.getLineOffset(my_start);
			int my_end_offset;
			if (my_document.getNumberOfLines() > my_end + 1)
				my_end_offset = my_document.getLineOffset(my_end + 1);
			else
				my_end_offset = my_document.getLineOffset(my_end) + my_document.getLineLength(my_end);

			return new Region(my_offset, my_end_offset - my_offset);

		} catch (BadLocationException x) {
			// concurrent modification
			return null;
		}
	}

	/* @region inner_classes */

	/**
	 * This class informs us if/when a (i.e. any) Java element has changed and
	 * makes sure that if we need to deal with the change, it is dealt with.
	 * @author phosphorus and others
	 *
	 */
	private class ElementChangedListener implements IElementChangedListener {

		/**
		 * Implementation of the <code>IElementChangedListener</code>
		 * method. Deals with the changes in the structure when the source
		 * code that we work on is changed.
		 */
		public void elementChanged(ElementChangedEvent an_event) {

			/* If our Structure provider is installed, we have an annotation model to use
			 * and we have a change that concerns us... 
			 */
			if (isInstalled() &&  (my_annotation_model != null) && isValidEvent(an_event.getDelta())) {
				updateStructure();
				updateAnnotations();
			}
		}


		private boolean isValidEvent(IJavaElementDelta a_delta) {

			/* I don't really understand the last part of this... */
			if (a_delta == null || a_delta.getElement().getElementType() > IJavaElement.CLASS_FILE) {
				return false;
			}

			/* If we work with this element, we have a valid event. */
			if(my_input.equals(a_delta.getElement())) {
				return true;
			}


			IJavaElementDelta[] some_children = a_delta.getAffectedChildren();

			/* If this change didn't affect any children, we don't have to touch anything.*/
			if (some_children == null || some_children.length == 0)
				return false;

			/* If the change did affect some children, check if any of those concerns us...*/
			boolean a_child_result = false;
			for (int i= 0; i < some_children.length; i++) {
				a_child_result = a_child_result || isValidEvent(some_children[i]);				
			}

			return a_child_result;
		}

	}

	/**
	 * This class informs us when the projection viewer is in projection mode
	 * and when not. 
	 * @author phosphorus, Coffee-Bytes.com, and others
	 *
	 */
	private class ProjectionListener implements IProjectionListener {

		/**
		 * What to do when the projection mode of the projection viewer is enabled?
		 * Do the stuff that needs to be done when it is disabled (just to make sure
		 * that everything is clean) and then (if the editor it supported) initialise
		 * the foldingStructureProvider and add a listener for changed elements.
		 */
		public void projectionEnabled() {
			projectionDisabled();

			if (isSupported(my_editor)) {
				//initialise the provider
				initialize();
				//and add the listener
				my_element_changed_listener = new ElementChangedListener();
				JavaCore.addElementChangedListener(my_element_changed_listener);
			}

		}

		/**
		 * What to do when the projection mode of the projection viewer is disabled?
		 * Release the document in use and remove the <code>ElementChangedListener</code>. 
		 */
		public void projectionDisabled() {
			JavaCore.removeElementChangedListener(my_element_changed_listener);
			my_element_changed_listener = null;
		}

	}

}

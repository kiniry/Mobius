package bonIDE.diagram.edit.parts;

import java.util.Collections;
import java.util.List;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.FlowLayoutEditPolicy;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.handles.MoveHandle;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.ui.editparts.AbstractBorderedShapeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IBorderItemEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.BorderItemSelectionEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ConstrainedToolbarLayoutEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.figures.BorderItemLocator;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Display;

/**
 * @generated
 */
public class IndexClauseEditPart extends ShapeNodeEditPart {

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 3003;

	/**
	 * @generated
	 */
	protected IFigure contentPane;

	/**
	 * @generated
	 */
	protected IFigure primaryShape;

	/**
	 * @generated
	 */
	public IndexClauseEditPart(View view) {
		super(view);
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE, new bonIDE.diagram.edit.policies.IndexClauseItemSemanticEditPolicy());
		installEditPolicy(EditPolicy.LAYOUT_ROLE, createLayoutEditPolicy());
		// XXX need an SCR to runtime to have another abstract superclass that would let children add reasonable editpolicies
		// removeEditPolicy(org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles.CONNECTION_HANDLES_ROLE);
	}

	/**
	 * @generated
	 */
	protected LayoutEditPolicy createLayoutEditPolicy() {

		ConstrainedToolbarLayoutEditPolicy lep = new ConstrainedToolbarLayoutEditPolicy() {

			protected EditPolicy createChildEditPolicy(EditPart child) {
				if (child.getEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE) == null) {
					if (child instanceof ITextAwareEditPart) {
						return new bonIDE.diagram.edit.policies.BonideTextSelectionEditPolicy();
					}
				}
				return super.createChildEditPolicy(child);
			}
		};
		return lep;
	}

	/**
	 * @generated
	 */
	protected IFigure createNodeShape() {
		IndexFigure figure = new IndexFigure();
		return primaryShape = figure;
	}

	/**
	 * @generated
	 */
	public IndexFigure getPrimaryShape() {
		return (IndexFigure) primaryShape;
	}

	/**
	 * @generated
	 */
	protected boolean addFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart) {
			((bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart) childEditPart).setLabel(getPrimaryShape().getFigureIndexIdentifierFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.IndexClauseTermsEditPart) {
			((bonIDE.diagram.edit.parts.IndexClauseTermsEditPart) childEditPart).setLabel(getPrimaryShape().getFigureIndexTermsFigure());
			return true;
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected boolean removeFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.IndexClauseTermsEditPart) {
			return true;
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected void addChildVisual(EditPart childEditPart, int index) {
		if (addFixedChild(childEditPart)) {
			return;
		}
		super.addChildVisual(childEditPart, -1);
	}

	/**
	 * @generated
	 */
	protected void removeChildVisual(EditPart childEditPart) {
		if (removeFixedChild(childEditPart)) {
			return;
		}
		super.removeChildVisual(childEditPart);
	}

	/**
	 * @generated
	 */
	protected IFigure getContentPaneFor(IGraphicalEditPart editPart) {
		return getContentPane();
	}

	/**
	 * @generated NOT
	 */
	protected NodeFigure createNodePlate() {
		DefaultSizeNodeFigure result = new DefaultSizeNodeFigure(40, 12);
		return result;
	}

	/**
	 * Creates figure for this edit part.
	 * 
	 * Body of this method does not depend on settings in generation model
	 * so you may safely remove <i>generated</i> tag and modify it.
	 * 
	 * @generated
	 */
	protected NodeFigure createNodeFigure() {
		NodeFigure figure = createNodePlate();
		figure.setLayoutManager(new StackLayout());
		IFigure shape = createNodeShape();
		figure.add(shape);
		contentPane = setupContentPane(shape);
		return figure;
	}

	/**
	 * Default implementation treats passed figure as content pane.
	 * Respects layout one may have set for generated figure.
	 * @param nodeShape instance of generated figure class
	 * @generated
	 */
	protected IFigure setupContentPane(IFigure nodeShape) {
		if (nodeShape.getLayoutManager() == null) {
			ConstrainedToolbarLayout layout = new ConstrainedToolbarLayout();
			layout.setSpacing(5);
			nodeShape.setLayoutManager(layout);
		}
		return nodeShape; // use nodeShape itself as contentPane
	}

	/**
	 * @generated
	 */
	public IFigure getContentPane() {
		if (contentPane != null) {
			return contentPane;
		}
		return super.getContentPane();
	}

	/**
	 * @generated
	 */
	protected void setForegroundColor(Color color) {
		if (primaryShape != null) {
			primaryShape.setForegroundColor(color);
		}
	}

	/**
	 * @generated
	 */
	protected void setBackgroundColor(Color color) {
		if (primaryShape != null) {
			primaryShape.setBackgroundColor(color);
		}
	}

	/**
	 * @generated
	 */
	protected void setLineWidth(int width) {
		if (primaryShape instanceof Shape) {
			((Shape) primaryShape).setLineWidth(width);
		}
	}

	/**
	 * @generated
	 */
	protected void setLineType(int style) {
		if (primaryShape instanceof Shape) {
			((Shape) primaryShape).setLineStyle(style);
		}
	}

	/**
	 * @generated
	 */
	public EditPart getPrimaryChildEditPart() {
		return getChildBySemanticHint(bonIDE.diagram.part.BonideVisualIDRegistry
				.getType(bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart.VISUAL_ID));
	}

	/**
	 * @generated
	 */
	public class IndexFigure extends RectangleFigure {

		/**
		 * @generated
		 */
		private RectangleFigure fFigureIndexFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureIndexIdentifierFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureIndexTermsFigure;

		/**
		 * @generated
		 */
		public IndexFigure() {

			ToolbarLayout layoutThis = new ToolbarLayout();
			layoutThis.setStretchMinorAxis(true);
			layoutThis.setMinorAlignment(ToolbarLayout.ALIGN_TOPLEFT
					);

			layoutThis.setSpacing(2);
			layoutThis.setVertical(false);

			this.setLayoutManager(layoutThis);

			this.setFill(false);
			this.setOutline(false);
			this.setLineWidth(1);
			createContents();
		}

		/**
		 * @generated
		 */
		private void createContents() {

			fFigureIndexIdentifierFigure = new WrappingLabel();
			fFigureIndexIdentifierFigure.setText("");
			fFigureIndexIdentifierFigure.setForegroundColor(FFIGUREINDEXIDENTIFIERFIGURE_FORE
					);

			fFigureIndexIdentifierFigure.setFont(FFIGUREINDEXIDENTIFIERFIGURE_FONT);

			this.add(fFigureIndexIdentifierFigure);

			fFigureIndexTermsFigure = new WrappingLabel();
			fFigureIndexTermsFigure.setText("");
			fFigureIndexTermsFigure.setForegroundColor(FFIGUREINDEXTERMSFIGURE_FORE
					);

			fFigureIndexTermsFigure.setFont(FFIGUREINDEXTERMSFIGURE_FONT);

			this.add(fFigureIndexTermsFigure);

		}

		/**
		 * @generated
		 */
		private boolean myUseLocalCoordinates = false;

		/**
		 * @generated
		 */
		protected boolean useLocalCoordinates() {
			return myUseLocalCoordinates;
		}

		/**
		 * @generated
		 */
		protected void setUseLocalCoordinates(boolean useLocalCoordinates) {
			myUseLocalCoordinates = useLocalCoordinates;
		}

		/**
		 * @generated
		 */
		public RectangleFigure getFigureIndexFigure() {
			return fFigureIndexFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureIndexIdentifierFigure() {
			return fFigureIndexIdentifierFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureIndexTermsFigure() {
			return fFigureIndexTermsFigure;
		}

	}

	/**
	 * @generated
	 */
	static final Color FFIGUREINDEXIDENTIFIERFIGURE_FORE = new Color(null, 0, 0, 200);

	/**
	 * @generated
	 */
	static final Font FFIGUREINDEXIDENTIFIERFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Color FFIGUREINDEXTERMSFIGURE_FORE = new Color(null, 0, 0, 128);

	/**
	 * @generated
	 */
	static final Font FFIGUREINDEXTERMSFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.NORMAL);

}

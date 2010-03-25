package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.FlowLayoutEditPolicy;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ConstrainedToolbarLayoutEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
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
public class FeatureArgumentEditPart extends ShapeNodeEditPart {

	/* (non-Javadoc)
	 * @see org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeEditPart#refreshBounds()
	 */
	@Override
	protected void refreshBounds() {
		System.out.println("FeatureArgumentEditPart.refreshBounds");
		super.refreshBounds();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeEditPart#refreshVisuals()
	 */
	@Override
	protected void refreshVisuals() {
		System.out.println("FeatureArgumentEditPart.refreshVisuals");
		// TODO Auto-generated method stub
		super.refreshVisuals();
	}

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 3007;

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
	public FeatureArgumentEditPart(View view) {
		super(view);
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE, new bonIDE.diagram.edit.policies.FeatureArgumentItemSemanticEditPolicy());
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
		ArgumentFigure figure = new ArgumentFigure();
		return primaryShape = figure;
	}

	/**
	 * @generated
	 */
	public ArgumentFigure getPrimaryShape() {
		return (ArgumentFigure) primaryShape;
	}

	/**
	 * @generated
	 */
	protected boolean addFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart) {
			((bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureArgumentNameFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart) {
			((bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureArgumentTypeFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart) {
			((bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureArgumentCollectionFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.WrappingLabel2EditPart) {
			((bonIDE.diagram.edit.parts.WrappingLabel2EditPart) childEditPart).setLabel(getPrimaryShape().getFigureArgumentArrowFigure());
			return true;
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected boolean removeFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.WrappingLabel2EditPart) {
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
				.getType(bonIDE.diagram.edit.parts.WrappingLabel2EditPart.VISUAL_ID));
	}

	/**
	 * @generated
	 */
	public class ArgumentFigure extends RectangleFigure {

		/**
		 * @generated
		 */
		private WrappingLabel fFigureArgumentArrowFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureArgumentNameFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureArgumentCollectionFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureArgumentTypeFigure;

		/**
		 * @generated
		 */
		public ArgumentFigure() {

			ToolbarLayout layoutThis = new ToolbarLayout();
			layoutThis.setStretchMinorAxis(false);
			layoutThis.setMinorAlignment(ToolbarLayout.ALIGN_TOPLEFT);

			layoutThis.setSpacing(1);
			layoutThis.setVertical(false);

			this.setLayoutManager(layoutThis);

			this.setFill(false);
			this.setOutline(false);
			this.setLineWidth(1);
			this.setForegroundColor(THIS_FORE);
			createContents();
		}

		/**
		 * @generated
		 */
		private void createContents() {

			fFigureArgumentArrowFigure = new WrappingLabel();
			fFigureArgumentArrowFigure.setText("\u2192");
			fFigureArgumentArrowFigure.setForegroundColor(FFIGUREARGUMENTARROWFIGURE_FORE);

			fFigureArgumentArrowFigure.setFont(FFIGUREARGUMENTARROWFIGURE_FONT);

			this.add(fFigureArgumentArrowFigure);

			fFigureArgumentNameFigure = new WrappingLabel();
			fFigureArgumentNameFigure.setText("");
			fFigureArgumentNameFigure.setForegroundColor(FFIGUREARGUMENTNAMEFIGURE_FORE);

			fFigureArgumentNameFigure.setFont(FFIGUREARGUMENTNAMEFIGURE_FONT);

			this.add(fFigureArgumentNameFigure);

			fFigureArgumentCollectionFigure = new WrappingLabel();
			fFigureArgumentCollectionFigure.setText("");
			fFigureArgumentCollectionFigure.setForegroundColor(FFIGUREARGUMENTCOLLECTIONFIGURE_FORE);

			fFigureArgumentCollectionFigure.setFont(FFIGUREARGUMENTCOLLECTIONFIGURE_FONT);

			this.add(fFigureArgumentCollectionFigure);

			fFigureArgumentTypeFigure = new WrappingLabel();
			fFigureArgumentTypeFigure.setText("");
			fFigureArgumentTypeFigure.setForegroundColor(FFIGUREARGUMENTTYPEFIGURE_FORE);

			fFigureArgumentTypeFigure.setFont(FFIGUREARGUMENTTYPEFIGURE_FONT);

			this.add(fFigureArgumentTypeFigure);

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
		public WrappingLabel getFigureArgumentArrowFigure() {
			return fFigureArgumentArrowFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureArgumentNameFigure() {
			return fFigureArgumentNameFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureArgumentCollectionFigure() {
			return fFigureArgumentCollectionFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureArgumentTypeFigure() {
			return fFigureArgumentTypeFigure;
		}

	}

	/**
	 * @generated
	 */
	static final Color THIS_FORE = new Color(null, 200, 0, 0);

	/**
	 * @generated
	 */
	static final Color FFIGUREARGUMENTARROWFIGURE_FORE = new Color(null, 0, 0, 128);

	/**
	 * @generated
	 */
	static final Font FFIGUREARGUMENTARROWFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Color FFIGUREARGUMENTNAMEFIGURE_FORE = new Color(null, 0, 0, 128);

	/**
	 * @generated
	 */
	static final Font FFIGUREARGUMENTNAMEFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.ITALIC);

	/**
	 * @generated
	 */
	static final Color FFIGUREARGUMENTCOLLECTIONFIGURE_FORE = new Color(null, 0, 0, 200);

	/**
	 * @generated
	 */
	static final Font FFIGUREARGUMENTCOLLECTIONFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.ITALIC);

	/**
	 * @generated
	 */
	static final Color FFIGUREARGUMENTTYPEFIGURE_FORE = new Color(null, 0, 0, 200);

	/**
	 * @generated
	 */
	static final Font FFIGUREARGUMENTTYPEFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7, SWT.ITALIC);

}

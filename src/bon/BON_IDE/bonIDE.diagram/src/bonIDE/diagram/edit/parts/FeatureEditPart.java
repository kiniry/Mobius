package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.FlowLayoutEditPolicy;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.core.edithelpers.CreateElementRequestAdapter;
import org.eclipse.gmf.runtime.diagram.ui.editparts.GraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ConstrainedToolbarLayoutEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CreationEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.DragDropEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateViewAndElementRequest;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
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
public class FeatureEditPart extends ShapeNodeEditPart {

	
	/* (non-Javadoc)
	 * @see org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeEditPart#refreshVisuals()
	 */
	@Override
	protected void refreshVisuals() {
		// TODO Auto-generated method stub
		System.out.println("FeatureEditPart.refreshVisuals");
		super.refreshVisuals();
		
	}

	/**
	 * @generated NOT
	 */
	@Override
	protected void refreshBounds() {
		// TODO Auto-generated method stub
		System.out.println("FeatureEditPart.refreshBounds");
		super.refreshBounds();
	}

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 3006;

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
	public FeatureEditPart(View view) {
		super(view);
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
				new bonIDE.diagram.edit.policies.FeatureItemSemanticEditPolicy());
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
		FeatureFigure figure = new FeatureFigure();
		return primaryShape = figure;
	}

	/**
	 * @generated
	 */
	public FeatureFigure getPrimaryShape() {
		return (FeatureFigure) primaryShape;
	}

	/**
	 * @generated
	 */
	protected boolean addFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureNamesEditPart) {
			((bonIDE.diagram.edit.parts.FeatureNamesEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureFeatureNamesFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureTypeEditPart) {
			((bonIDE.diagram.edit.parts.FeatureTypeEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureFeatureTypeFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureCommentEditPart) {
			((bonIDE.diagram.edit.parts.FeatureCommentEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureFeatureCommentFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureModifierEditPart) {
			((bonIDE.diagram.edit.parts.FeatureModifierEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureFeatureModifierFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigurePostConditionsRectangeFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane.add(((bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart) childEditPart).getFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigurePreConditionsRectangleFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane.add(((bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart) childEditPart).getFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigureFeatureArgumentsRectangleFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane.add(((bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart) childEditPart).getFigure());
			return true;
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected boolean removeFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureNamesEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureTypeEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureCommentEditPart) {					
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureModifierEditPart) {
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigurePostConditionsRectangeFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane
					.remove(((bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart) childEditPart)
							.getFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigurePreConditionsRectangleFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane.remove(((bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart) childEditPart).getFigure());
			return true;
		}
		if (childEditPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart) {
			IFigure pane = getPrimaryShape().getFigureFeatureArgumentsRectangleFigure();
			setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
			pane.remove(((bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart) childEditPart).getFigure());
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
		if (editPart instanceof bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart) {
			return getPrimaryShape().getFigurePostConditionsRectangeFigure();
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart) {
			return getPrimaryShape().getFigurePreConditionsRectangleFigure();
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart) {
			return getPrimaryShape().getFigureFeatureArgumentsRectangleFigure();
		}
		return getContentPane();
	}

	/**
	 * @generated
	 */
	protected NodeFigure createNodePlate() {
		DefaultSizeNodeFigure result = new DefaultSizeNodeFigure(40, 5);
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
				.getType(bonIDE.diagram.edit.parts.FeatureNamesEditPart.VISUAL_ID));
	}

	/**
	 * @generated
	 */
	public EditPart getTargetEditPart(Request request) {
		if (request instanceof CreateViewAndElementRequest) {
			CreateElementRequestAdapter adapter = ((CreateViewAndElementRequest) request).getViewAndElementDescriptor()
					.getCreateElementRequestAdapter();
			IElementType type = (IElementType) adapter.getAdapter(IElementType.class);
			if (type == bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009) {
				return getChildBySemanticHint(bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart.VISUAL_ID));
			}
			if (type == bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008) {
				return getChildBySemanticHint(bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart.VISUAL_ID));
			}
			if (type == bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007) {
				return getChildBySemanticHint(bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart.VISUAL_ID));
			}
		}
		return super.getTargetEditPart(request);
	}

	/**
	 * @generated
	 */
	public class FeatureFigure extends RectangleFigure {

		/**
		 * @generated
		 */
		private WrappingLabel fFigureFeatureNamesFigure;
		/**
		 * @generated
		 */
		private RectangleFigure fFigureFeatureSignatureRectangleFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureFeatureModifierFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureFeatureTypeFigure;

		/**
		 * @generated
		 */
		private WrappingLabel fFigureFeatureCommentFigure;
		/**
		 * @generated
		 */
		private RectangleFigure fFigureFeatureArgumentsRectangleFigure;

		/**
		 * @generated
		 */
		private RectangleFigure fFigurePreConditionsRectangleFigure;
		/**
		 * @generated
		 */
		private RectangleFigure fFigurePostConditionsRectangeFigure;

		/**
		 * @generated
		 */
		public FeatureFigure() {

			/*ToolbarLayout layoutThis = new ToolbarLayout();
			layoutThis.setStretchMinorAxis(false);
			layoutThis.setMinorAlignment(ToolbarLayout.ALIGN_TOPLEFT);

			layoutThis.setSpacing(0);
			layoutThis.setVertical(true);*/
			
			ConstrainedToolbarLayout layoutThis = new ConstrainedToolbarLayout();
			layoutThis.setStretchMajorAxis(true);
			layoutThis.setStretchMinorAxis(true);
			layoutThis.setMinorAlignment(ConstrainedToolbarLayout.ALIGN_TOPLEFT);
			
			this.setLayoutManager(layoutThis);

			this.setLineWidth(1);
			this.setForegroundColor(THIS_FORE);
			//this.setSize(10, 5);
			//this.setMinimumSize();
			//this.setPreferredSize(new Dimension(10,5));
			
			createContents();
		}

		/**
		 * @generated
		 */
		private void createContents() {

			fFigureFeatureSignatureRectangleFigure = new RectangleFigure();
			fFigureFeatureSignatureRectangleFigure.setLineWidth(1);
			fFigureFeatureSignatureRectangleFigure.setForegroundColor(FFIGUREFEATURESIGNATURERECTANGLEFIGURE_FORE);

			this.add(fFigureFeatureSignatureRectangleFigure);

			ToolbarLayout layoutFFigureFeatureSignatureRectangleFigure = new ToolbarLayout();
			layoutFFigureFeatureSignatureRectangleFigure.setStretchMinorAxis(false);
			layoutFFigureFeatureSignatureRectangleFigure.setMinorAlignment(ToolbarLayout.ALIGN_TOPLEFT);

			layoutFFigureFeatureSignatureRectangleFigure.setSpacing(0);
			layoutFFigureFeatureSignatureRectangleFigure.setVertical(false);

			fFigureFeatureSignatureRectangleFigure.setLayoutManager(layoutFFigureFeatureSignatureRectangleFigure);

			fFigureFeatureNamesFigure = new WrappingLabel();
			fFigureFeatureNamesFigure.setText("<...>");

			fFigureFeatureNamesFigure.setFont(FFIGUREFEATURENAMESFIGURE_FONT);

			fFigureFeatureSignatureRectangleFigure.add(fFigureFeatureNamesFigure);

			fFigureFeatureModifierFigure = new WrappingLabel();
			fFigureFeatureModifierFigure.setText("");

			fFigureFeatureModifierFigure.setFont(FFIGUREFEATUREMODIFIERFIGURE_FONT);

			fFigureFeatureSignatureRectangleFigure.add(fFigureFeatureModifierFigure);

			fFigureFeatureTypeFigure = new WrappingLabel();
			fFigureFeatureTypeFigure.setText("");

			fFigureFeatureTypeFigure.setFont(FFIGUREFEATURETYPEFIGURE_FONT);

			fFigureFeatureSignatureRectangleFigure.add(fFigureFeatureTypeFigure);

			fFigureFeatureCommentFigure = new WrappingLabel();			
			fFigureFeatureCommentFigure.setText("");

			fFigureFeatureCommentFigure.setFont(FFIGUREFEATURECOMMENTFIGURE_FONT);

			this.add(fFigureFeatureCommentFigure);

			fFigureFeatureArgumentsRectangleFigure = new RectangleFigure();
			fFigureFeatureArgumentsRectangleFigure.setLineWidth(1);
			fFigureFeatureArgumentsRectangleFigure.setForegroundColor(FFIGUREFEATUREARGUMENTSRECTANGLEFIGURE_FORE);

			this.add(fFigureFeatureArgumentsRectangleFigure);

			FlowLayout layoutFFigureFeatureArgumentsRectangleFigure = new FlowLayout();
			layoutFFigureFeatureArgumentsRectangleFigure.setStretchMinorAxis(false);
			layoutFFigureFeatureArgumentsRectangleFigure.setMinorAlignment(FlowLayout.ALIGN_LEFTTOP);

			layoutFFigureFeatureArgumentsRectangleFigure.setMajorAlignment(FlowLayout.ALIGN_LEFTTOP);
			layoutFFigureFeatureArgumentsRectangleFigure.setMajorSpacing(1);
			layoutFFigureFeatureArgumentsRectangleFigure.setMinorSpacing(1);
			layoutFFigureFeatureArgumentsRectangleFigure.setHorizontal(true);

			fFigureFeatureArgumentsRectangleFigure.setLayoutManager(layoutFFigureFeatureArgumentsRectangleFigure);

			fFigurePreConditionsRectangleFigure = new RectangleFigure();
			fFigurePreConditionsRectangleFigure.setLineWidth(1);
			fFigurePreConditionsRectangleFigure.setForegroundColor(FFIGUREPRECONDITIONSRECTANGLEFIGURE_FORE);

			this.add(fFigurePreConditionsRectangleFigure);

			FlowLayout layoutFFigurePreConditionsRectangleFigure = new FlowLayout();
			layoutFFigurePreConditionsRectangleFigure.setStretchMinorAxis(false);
			layoutFFigurePreConditionsRectangleFigure.setMinorAlignment(FlowLayout.ALIGN_LEFTTOP);

			layoutFFigurePreConditionsRectangleFigure.setMajorAlignment(FlowLayout.ALIGN_LEFTTOP);
			layoutFFigurePreConditionsRectangleFigure.setMajorSpacing(5);
			layoutFFigurePreConditionsRectangleFigure.setMinorSpacing(5);
			layoutFFigurePreConditionsRectangleFigure.setHorizontal(true);

			fFigurePreConditionsRectangleFigure.setLayoutManager(layoutFFigurePreConditionsRectangleFigure);

			fFigurePostConditionsRectangeFigure = new RectangleFigure();
			fFigurePostConditionsRectangeFigure.setLineWidth(1);
			fFigurePostConditionsRectangeFigure.setForegroundColor(FFIGUREPOSTCONDITIONSRECTANGEFIGURE_FORE);

			this.add(fFigurePostConditionsRectangeFigure);

			FlowLayout layoutFFigurePostConditionsRectangeFigure = new FlowLayout();
			layoutFFigurePostConditionsRectangeFigure.setStretchMinorAxis(false);
			layoutFFigurePostConditionsRectangeFigure.setMinorAlignment(FlowLayout.ALIGN_LEFTTOP);

			layoutFFigurePostConditionsRectangeFigure.setMajorAlignment(FlowLayout.ALIGN_LEFTTOP);
			layoutFFigurePostConditionsRectangeFigure.setMajorSpacing(5);
			layoutFFigurePostConditionsRectangeFigure.setMinorSpacing(5);
			layoutFFigurePostConditionsRectangeFigure.setHorizontal(true);

			fFigurePostConditionsRectangeFigure.setLayoutManager(layoutFFigurePostConditionsRectangeFigure);
			
		}

		/**
		 * @generated NOT
		 */
		public void hideComponent(GraphicalEditPart component){
			if( component instanceof FeatureCommentEditPart){
				fFigureFeatureCommentFigure.setVisible(false);
			
			}			
		}
		
		/**
		 * @generated NOT
		 */
		public void showComponent(GraphicalEditPart component){
			if( component instanceof FeatureCommentEditPart){
				fFigureFeatureCommentFigure.setVisible(true);
			}else if ( component instanceof FeatureCommentEditPart){
				//this.fFigurePreConditionsRectangleFigure
			}
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
		public WrappingLabel getFigureFeatureNamesFigure() {
			return fFigureFeatureNamesFigure;
		}

		/**
		 * @generated
		 */
		public RectangleFigure getFigureFeatureSignatureRectangleFigure() {
			return fFigureFeatureSignatureRectangleFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureFeatureModifierFigure() {
			return fFigureFeatureModifierFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureFeatureTypeFigure() {
			return fFigureFeatureTypeFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureFeatureCommentFigure() {
			return fFigureFeatureCommentFigure;
		}

		/**
		 * @generated
		 */
		public RectangleFigure getFigureFeatureArgumentsRectangleFigure() {
			return fFigureFeatureArgumentsRectangleFigure;
		}

		/**
		 * @generated
		 */
		public RectangleFigure getFigurePreConditionsRectangleFigure() {
			return fFigurePreConditionsRectangleFigure;
		}

		/**
		 * @generated
		 */
		public RectangleFigure getFigurePostConditionsRectangeFigure() {
			return fFigurePostConditionsRectangeFigure;
		}

	}

	/**
	 * @generated
	 */
	static final Color THIS_FORE = new Color(null, 255, 67, 226);

	/**
	 * @generated
	 */
	static final Color FFIGUREFEATURESIGNATURERECTANGLEFIGURE_FORE = new Color(null, 0, 0, 200);

	/**
	 * @generated
	 */
	static final Font FFIGUREFEATURENAMESFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7,
			SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Font FFIGUREFEATUREMODIFIERFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7,
			SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Font FFIGUREFEATURETYPEFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7,
			SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Font FFIGUREFEATURECOMMENTFIGURE_FONT = new Font(Display.getCurrent(), "Lucida Sans Unicode", 7,
			SWT.NORMAL);

	/**
	 * @generated
	 */
	static final Color FFIGUREFEATUREARGUMENTSRECTANGLEFIGURE_FORE = new Color(null, 255, 255, 64);

	/**
	 * @generated
	 */
	static final Color FFIGUREPRECONDITIONSRECTANGLEFIGURE_FORE = new Color(null, 192, 192, 0);

	/**
	 * @generated
	 */
	static final Color FFIGUREPOSTCONDITIONSRECTANGEFIGURE_FORE = new Color(null, 255, 128, 128);

}

package bonIDE.diagram.edit.parts;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.BorderLayout;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.RoundedRectangle;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.command.SetCommand;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editparts.AbstractEditPart;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.editpolicies.ResizableEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.commands.SetBoundsCommand;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.commands.SetValueCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.SetRequest;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.NotationPackage;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;
import org.eclipse.core.runtime.IAdaptable;

import bonIDE.BonIDEPackage;
import bonIDE.Cluster;

/**
 * @generated
 */
public class ClusterEditPart extends ShapeNodeEditPart {

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 2001;

	/**
	 * @generated
	 */
	protected IFigure contentPane;

	/**
	 * @generated
	 */
	protected IFigure primaryShape;

	/**
	 * @generated NOT
	 */
	protected boolean collapsedStateChanged;

	/**
	 * @generated
	 */
	public ClusterEditPart(View view) {
		super(view);
	}

	/**
	 * @generated NOT
	 */
	public void setCollapsed(boolean collapsed) {
		this.getEditingDomain().getCommandStack().execute(
				SetCommand.create(
				getEditingDomain(),
				getNotationView().getElement(),
				BonIDEPackage.eINSTANCE.getCluster_Collapsed(),
				collapsed));
	}

	/**
	 * @generated NOT
	 */
	public void setExpandedHeight(int expandedHeight) {
		this.getEditingDomain().getCommandStack().execute(
				SetCommand.create(
				getEditingDomain(),
				getNotationView().getElement(),
				BonIDEPackage.eINSTANCE.getCluster_ExpandedHeight(),
				expandedHeight));
	}

	/*
	 * @generated NOT 
	 * 
	 * @seeorg.eclipse.gmf.runtime.diagram.ui.editparts.ShapeEditPart#
	 * getPrimaryDragEditPolicy()
	 */
	@Override
	public EditPolicy getPrimaryDragEditPolicy() {
		EditPolicy result = super.getPrimaryDragEditPolicy();
		if (result instanceof ResizableEditPolicy) {
			ResizableEditPolicy ep = (ResizableEditPolicy) result;

			if (((Cluster) (this.getNotationView().getElement())).isCollapsed()) {
				ep.setResizeDirections(PositionConstants.NONE);
			} else {
				ep.setResizeDirections(PositionConstants.NSEW);
			}
			this.installEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE, ep);
		}
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @generated NOT
	 * 
	 * @see
	 * org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeEditPart#refreshBounds
	 * ()
	 */
	@Override
	protected void refreshBounds() {
		System.out.println("refreshBounds");

		// set the cluster name text alignment - it would be preferable to do this in 
		// ClusterFigure.createContents(), but if it's done here, it's one less method
		// maintain, and we can leave ClusterFigure.createContents() as '@generated' 
		this.getPrimaryShape().getFigureClusterNameFigure().setAlignment(PositionConstants.CENTER);
		
		if (this.collapsedStateChanged == false) {
			super.refreshBounds();
		} else {
			this.collapsedStateChanged = false;

			int width = ((Integer) this.getStructuralFeatureValue(NotationPackage.eINSTANCE.getSize_Width())).intValue();
			int height = ((Integer) this.getStructuralFeatureValue(NotationPackage.eINSTANCE.getSize_Height())).intValue();
			int x = ((Integer) this.getStructuralFeatureValue(NotationPackage.eINSTANCE.getLocation_X())).intValue();
			int y = ((Integer) this.getStructuralFeatureValue(NotationPackage.eINSTANCE.getLocation_Y())).intValue();
			boolean isClusterCollapsed = ((Cluster) (this.getNotationView().getElement())).isCollapsed();

			if (isClusterCollapsed == false) {
				// expanding
				height  = ((Cluster) (this.getNotationView().getElement())).getExpandedHeight();				
			} else {
				// collapsing, need to remember the current (expanded) height
				setExpandedHeight(height);
				height = 28;
			}

			Dimension size = new Dimension(width, height);	
			Point location = new Point(x, y);

			SetBoundsCommand boundsCommand = new SetBoundsCommand(
					this.getEditingDomain(),
					"",
					new EObjectAdapter((View) this.getModel()),
					new Rectangle(location, size));

			this.getDiagramEditDomain().getDiagramCommandStack().execute(new ICommandProxy(boundsCommand));				
			this.getPrimaryDragEditPolicy();
		}
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
				new bonIDE.diagram.edit.policies.ClusterItemSemanticEditPolicy());
		installEditPolicy(EditPolicy.LAYOUT_ROLE, createLayoutEditPolicy());
		// XXX need an SCR to runtime to have another abstract superclass that would let children add reasonable editpolicies
		// removeEditPolicy(org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles.CONNECTION_HANDLES_ROLE);
	}

	/**
	 * @generated
	 */
	protected LayoutEditPolicy createLayoutEditPolicy() {
		LayoutEditPolicy lep = new LayoutEditPolicy() {

			protected EditPolicy createChildEditPolicy(EditPart child) {
				EditPolicy result = child.getEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE);
				if (result == null) {
					result = new NonResizableEditPolicy();
				}
				return result;
			}

			protected Command getMoveChildrenCommand(Request request) {
				return null;
			}

			protected Command getCreateCommand(CreateRequest request) {
				return null;
			}
		};
		return lep;
	}

	/**
	 * @generated
	 */
	protected IFigure createNodeShape() {
		ClusterFigure figure = new ClusterFigure();
		return primaryShape = figure;
	}

	/**
	 * @generated
	 */
	public ClusterFigure getPrimaryShape() {
		return (ClusterFigure) primaryShape;
	}

	/**
	 * @generated
	 */
	protected boolean addFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.ClusterNameEditPart) {
			((bonIDE.diagram.edit.parts.ClusterNameEditPart) childEditPart).setLabel(getPrimaryShape()
					.getFigureClusterNameFigure());
			return true;
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected boolean removeFixedChild(EditPart childEditPart) {
		if (childEditPart instanceof bonIDE.diagram.edit.parts.ClusterNameEditPart) {
			return true;
		}
		return false;
	}

	/**
	 * @generated NOT
	 */
	protected void addChildVisual(EditPart childEditPart, int index) {
		if (addFixedChild(childEditPart)) {
			return;
		}
		super.addChildVisual(childEditPart, -1);

		// don't want to override super.addChildVisual, so
		// set the layout info of the child compartment here
		for (int i = 0; i < this.children.size(); i++) {
			AbstractEditPart childPart = (AbstractEditPart) this.children.get(i);

			if (childPart instanceof ClusterClusterCompartmentEditPart ||
					childPart instanceof ClusterClusterCompartment2EditPart) {
				ClusterClusterCompartmentEditPart ccEP = (ClusterClusterCompartmentEditPart) childPart;
				this.setLayoutConstraint(ccEP, ccEP.getFigure(), BorderLayout.CENTER);
				break;
			}
		}
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
	 * @generated
	 */
	protected NodeFigure createNodePlate() {
		DefaultSizeNodeFigure result = new DefaultSizeNodeFigure(40, 40);
		return result;
	}

	/**
	 * Creates figure for this edit part.
	 * 
	 * Body of this method does not depend on settings in generation model so
	 * you may safely remove <i>generated</i> tag and modify it.
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
	 * Default implementation treats passed figure as content pane. Respects
	 * layout one may have set for generated figure.
	 * 
	 * @param nodeShape
	 *            instance of generated figure class
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
				.getType(bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID));
	}

	private SetValueCommand setMultipleValueCommand(SetRequest request, final EObject element,
			final EAttribute eAttribute) {

		SetValueCommand operation = new SetValueCommand(request) {

			@Override
			protected IStatus doUndo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
				element.eSet(eAttribute, this.getRequest().getParameter("oldValue"));
				return Status.OK_STATUS;
			}

			@Override
			public boolean canUndo() {
				return true;
			}

			@Override
			protected IStatus doRedo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
				element.eSet(eAttribute, ((SetRequest) this.getRequest()).getValue());
				return Status.OK_STATUS;
			}

			@Override
			public boolean canRedo() {
				return true;
			}
		};
		return operation;
	}

	/**
	 * @generated
	 */
	public class ClusterFigure extends RoundedRectangle {

		/**
		 * @generated
		 */
		private RoundedRectangle fFigureClusterFigure;
		/**
		 * @generated
		 */
		private WrappingLabel fFigureClusterNameFigure;

		/**
		 * @generated
		 */
		public ClusterFigure() {

			BorderLayout layoutThis = new BorderLayout();
			this.setLayoutManager(layoutThis);

			this.setCornerDimensions(new Dimension(getMapMode().DPtoLP(8)
					, getMapMode().DPtoLP(8)));
			this.setLineWidth(1);
			this.setLineStyle(Graphics.LINE_DASH);
			this.setMinimumSize(new Dimension(getMapMode().DPtoLP(18)
					, getMapMode().DPtoLP(18)));
			createContents();
		}

		/**
		 * @generated
		 */
		private void createContents() {

			fFigureClusterNameFigure = new WrappingLabel();
			fFigureClusterNameFigure.setText("<...>");

			this.add(fFigureClusterNameFigure, BorderLayout.TOP);

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
		public RoundedRectangle getFigureClusterFigure() {
			return fFigureClusterFigure;
		}

		/**
		 * @generated
		 */
		public WrappingLabel getFigureClusterNameFigure() {
			return fFigureClusterNameFigure;
		}
	}

}

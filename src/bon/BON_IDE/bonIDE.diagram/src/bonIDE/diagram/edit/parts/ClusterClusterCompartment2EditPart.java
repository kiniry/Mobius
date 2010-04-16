package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.IFigure;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeCompartmentEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CreationEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.DragDropEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ResizableCompartmentEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.figures.ResizableCompartmentFigure;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.internal.figures.AnimatableScrollPane;
import org.eclipse.gmf.runtime.notation.NotationPackage;
import org.eclipse.gmf.runtime.notation.View;

import bonIDE.diagram.edit.parts.Cluster2EditPart.ClusterFigure;

/**
 * @generated
 */
public class ClusterClusterCompartment2EditPart extends ShapeCompartmentEditPart {

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 7002;

	/**
	 * @generated
	 */
	public ClusterClusterCompartment2EditPart(View view) {
		super(view);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @generated NOT
	 * 
	 * @see
	 * org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeCompartmentEditPart
	 * #handleNotificationEvent(org.eclipse.emf.common.notify.Notification)
	 */
	@Override
	protected void handleNotificationEvent(Notification event) {
		Object feature = event.getFeature();
		if (NotationPackage.eINSTANCE.getDrawerStyle_Collapsed().equals(feature)) {

			// the collapsed/expanded state of the compartment is changing; pass up the 
			// new status to the parent ClusterEditPart so it can draw itself accordingly 			
			setCollapsed(event.getNewBooleanValue(), true);

			boolean isCollapsed = event.getNewBooleanValue();

			Cluster2EditPart parentEditPart = (Cluster2EditPart) this.getParent();
			parentEditPart.SetCollapsed(isCollapsed);
			parentEditPart.collapsedStateChanged = true;
			parentEditPart.refreshBounds();

		}

		super.handleNotificationEvent(event);
	}

	/**
	 * @generated
	 */
	public String getCompartmentName() {
		return bonIDE.diagram.part.Messages.ClusterClusterCompartment2EditPart_title;
	}

	/**
	 * @generated
	 */
	public IFigure createFigure() {
		ResizableCompartmentFigure result = (ResizableCompartmentFigure) super.createFigure();
		result.setTitleVisibility(false);
		return result;
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE, new ResizableCompartmentEditPolicy());
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE, new bonIDE.diagram.edit.policies.ClusterClusterCompartment2ItemSemanticEditPolicy());
		installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
		installEditPolicy(EditPolicyRoles.DRAG_DROP_ROLE, new DragDropEditPolicy());
		installEditPolicy(EditPolicyRoles.CANONICAL_ROLE, new bonIDE.diagram.edit.policies.ClusterClusterCompartment2CanonicalEditPolicy());
	}

	/**
	 * @generated
	 */
	protected void setRatio(Double ratio) {
		if (getFigure().getParent().getLayoutManager() instanceof ConstrainedToolbarLayout) {
			super.setRatio(ratio);
		}
	}

}

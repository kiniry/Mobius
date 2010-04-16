package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.IFigure;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.gef.EditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ListCompartmentEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CreationEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.DragDropEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.figures.ResizableCompartmentFigure;
import org.eclipse.gmf.runtime.diagram.ui.internal.figures.NestedResizableCompartmentFigure;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.notation.View;

import bonIDE.diagram.custom.VeryThinResizableCompartmentFigure;

/**
 * @generated
 */
public class FeaturePostConditionCompartmentEditPart extends ListCompartmentEditPart {

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 7009;

	/**
	 * @generated
	 */
	public FeaturePostConditionCompartmentEditPart(View view) {
		super(view);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gmf.runtime.diagram.ui.editparts.GraphicalEditPart#addChild(org.eclipse.gef.EditPart, int)
	 */
	@Override
	protected void addChild(EditPart child, int index) {
		super.addChild(child, index);
		adjustVisibility();
	}

	/**
	 * @generated NOT
	 */
	protected void adjustVisibility() {
		if (this.getChildren().size() == 0) {
			FeatureEditPart parentFeature = (FeatureEditPart) this.getParent();
			parentFeature.getPrimaryShape().hideComponent(this);
		} else {
			FeatureEditPart parentFeature = (FeatureEditPart) this.getParent();
			parentFeature.getPrimaryShape().showComponent(this);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractEditPart#removeChild(org.eclipse.gef.EditPart)
	 */
	@Override
	protected void removeChild(EditPart child) {
		super.removeChild(child);
		adjustVisibility();
	}

	/**
	 * @generated
	 */
	protected boolean hasModelChildrenChanged(Notification evt) {
		return false;
	}

	/**
	 * @generated
	 */
	public String getCompartmentName() {
		return bonIDE.diagram.part.Messages.FeaturePostConditionCompartmentEditPart_title;
	}

	/**
	 * @generated NOT
	 */
	public IFigure createFigure() {
		ResizableCompartmentFigure rcf;
		if (getParent() == getTopGraphicEditPart()) {
			rcf = (ResizableCompartmentFigure) new VeryThinResizableCompartmentFigure(getCompartmentName(),
					getMapMode());
		} else {
			rcf = new NestedResizableCompartmentFigure(getMapMode());
		}

		ConstrainedToolbarLayout layout = new ConstrainedToolbarLayout();
		layout.setStretchMajorAxis(false);
		layout.setStretchMinorAxis(false);
		layout.setMinorAlignment(ConstrainedToolbarLayout.ALIGN_TOPLEFT);
		rcf.getContentPane().setLayoutManager(layout);

		rcf.setTitleVisibility(false);
		rcf.setBorder(null);
		adjustVisibility();
		return rcf;
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE, new bonIDE.diagram.edit.policies.FeaturePostConditionCompartmentItemSemanticEditPolicy());
		installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
		installEditPolicy(EditPolicyRoles.DRAG_DROP_ROLE, new DragDropEditPolicy());
		installEditPolicy(EditPolicyRoles.CANONICAL_ROLE, new bonIDE.diagram.edit.policies.FeaturePostConditionCompartmentCanonicalEditPolicy());
	}

	/**
	 * @generated
	 */
	protected void setRatio(Double ratio) {
		// nothing to do -- parent layout does not accept Double constraints as ratio
		// super.setRatio(ratio); 
	}

}

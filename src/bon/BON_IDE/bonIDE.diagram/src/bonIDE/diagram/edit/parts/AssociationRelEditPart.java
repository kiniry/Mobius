package bonIDE.diagram.edit.parts;

import org.eclipse.draw2d.Connection;
import org.eclipse.draw2d.ManhattanConnectionRouter;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITreeBranchEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.notation.View;

/**
 * @generated
 */
public class AssociationRelEditPart extends ConnectionNodeEditPart implements ITreeBranchEditPart {

	/**
	 * @generated
	 */
	public static final int VISUAL_ID = 4003;

	/**
	 * @generated
	 */
	public AssociationRelEditPart(View view) {
		super(view);
	}

	/*
	 * @generated NOT
	 */
	@Override
	protected void installRouter() {
		getConnectionFigure().setConnectionRouter(new ManhattanConnectionRouter());
		refreshRouterChange();
	}

	/**
	 * @generated
	 */
	protected void createDefaultEditPolicies() {
		super.createDefaultEditPolicies();
		installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE, new bonIDE.diagram.edit.policies.AssociationRelItemSemanticEditPolicy());
	}

	/**
	 * Creates figure for this edit part.
	 * 
	 * Body of this method does not depend on settings in generation model
	 * so you may safely remove <i>generated</i> tag and modify it.
	 * 
	 * @generated
	 */
	protected Connection createConnectionFigure() {
		return new bonIDE.diagram.custom.AssociationConnection();
	}

	/**
	 * @generated
	 */
	public bonIDE.diagram.custom.AssociationConnection getPrimaryShape() {
		return (bonIDE.diagram.custom.AssociationConnection) getFigure();
	}

}

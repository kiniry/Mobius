package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class BONClassInheritanceCompartmentItemSemanticEditPolicy extends
		bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public BONClassInheritanceCompartmentItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.InheritanceClauseCreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class BONClassIndexCompartmentItemSemanticEditPolicy extends bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public BONClassIndexCompartmentItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.IndexClauseCreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

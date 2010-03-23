package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class BONClassFeatureCompartmentItemSemanticEditPolicy extends bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public BONClassFeatureCompartmentItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.Feature_3006 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.FeatureCreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

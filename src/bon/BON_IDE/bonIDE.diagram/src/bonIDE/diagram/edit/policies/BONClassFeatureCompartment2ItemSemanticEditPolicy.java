package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class BONClassFeatureCompartment2ItemSemanticEditPolicy extends
		bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public BONClassFeatureCompartment2ItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.BONClass_2002);
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

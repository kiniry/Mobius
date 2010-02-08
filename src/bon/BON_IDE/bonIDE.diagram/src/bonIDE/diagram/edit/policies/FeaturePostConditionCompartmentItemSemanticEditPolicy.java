package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class FeaturePostConditionCompartmentItemSemanticEditPolicy extends
		bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public FeaturePostConditionCompartmentItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.Feature_3006);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.PostConditionCreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

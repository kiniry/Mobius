package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class FeaturePreConditionCompartmentItemSemanticEditPolicy extends
		bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public FeaturePreConditionCompartmentItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.Feature_3006);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.PreConditionCreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

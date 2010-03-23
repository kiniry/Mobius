package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;

/**
 * @generated
 */
public class AggregationRelItemSemanticEditPolicy extends bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public AggregationRelItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002);
	}

	/**
	 * @generated
	 */
	protected Command getDestroyElementCommand(DestroyElementRequest req) {
		return getGEFWrapper(new DestroyElementCommand(req));
	}

}

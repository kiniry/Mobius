package bonIDE.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

/**
 * @generated
 */
public class ClusterClusterCompartment2ItemSemanticEditPolicy extends
		bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public ClusterClusterCompartment2ItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.Cluster_3001);
	}

	/**
	 * @generated
	 */
	protected Command getCreateCommand(CreateElementRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.Cluster_3001 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.Cluster2CreateCommand(req));
		}
		if (bonIDE.diagram.providers.BonideElementTypes.BONClass_3002 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.BONClass2CreateCommand(req));
		}
		return super.getCreateCommand(req);
	}

}

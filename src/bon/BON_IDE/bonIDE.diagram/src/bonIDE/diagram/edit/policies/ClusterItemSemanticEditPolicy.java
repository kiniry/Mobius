package bonIDE.diagram.edit.policies;

import java.util.Iterator;

import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.common.core.command.ICompositeCommand;
import org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.View;

/**
 * @generated
 */
public class ClusterItemSemanticEditPolicy extends bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy {

	/**
	 * @generated
	 */
	public ClusterItemSemanticEditPolicy() {
		super(bonIDE.diagram.providers.BonideElementTypes.Cluster_2001);
	}

	/**
	 * @generated
	 */
	protected Command getDestroyElementCommand(DestroyElementRequest req) {
		View view = (View) getHost().getModel();
		CompositeTransactionalCommand cmd = new CompositeTransactionalCommand(getEditingDomain(), null);
		cmd.setTransactionNestingEnabled(false);
		for (Iterator it = view.getTargetEdges().iterator(); it.hasNext();) {
			Edge incomingLink = (Edge) it.next();
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
				continue;
			}
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
				continue;
			}
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
				continue;
			}
		}
		for (Iterator it = view.getSourceEdges().iterator(); it.hasNext();) {
			Edge outgoingLink = (Edge) it.next();
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
				continue;
			}
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
				continue;
			}
			if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
				DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
				cmd.add(new DestroyElementCommand(r));
				cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
				continue;
			}
		}
		EAnnotation annotation = view.getEAnnotation("Shortcut"); //$NON-NLS-1$
		if (annotation == null) {
			// there are indirectly referenced children, need extra commands: false
			addDestroyChildNodesCommand(cmd);
			addDestroyShortcutsCommand(cmd, view);
			// delete host element
			cmd.add(new DestroyElementCommand(req));
		} else {
			cmd.add(new DeleteCommand(getEditingDomain(), view));
		}
		return getGEFWrapper(cmd.reduce());
	}

	/**
	 * @generated
	 */
	private void addDestroyChildNodesCommand(ICompositeCommand cmd) {
		View view = (View) getHost().getModel();
		for (Iterator nit = view.getChildren().iterator(); nit.hasNext();) {
			Node node = (Node) nit.next();
			switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(node)) {
			case bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID:
				for (Iterator cit = node.getChildren().iterator(); cit.hasNext();) {
					Node cnode = (Node) cit.next();
					switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(cnode)) {
					case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
						for (Iterator it = cnode.getTargetEdges().iterator(); it.hasNext();) {
							Edge incomingLink = (Edge) it.next();
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
						}
						for (Iterator it = cnode.getSourceEdges().iterator(); it.hasNext();) {
							Edge outgoingLink = (Edge) it.next();
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
						}
						cmd.add(new DestroyElementCommand(new DestroyElementRequest(getEditingDomain(), cnode.getElement(), false))); // directlyOwned: true
						// don't need explicit deletion of cnode as parent's view deletion would clean child views as well 
						// cmd.add(new org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand(getEditingDomain(), cnode));
						break;
					case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
						for (Iterator it = cnode.getTargetEdges().iterator(); it.hasNext();) {
							Edge incomingLink = (Edge) it.next();
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(incomingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(incomingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), incomingLink));
								continue;
							}
						}
						for (Iterator it = cnode.getSourceEdges().iterator(); it.hasNext();) {
							Edge outgoingLink = (Edge) it.next();
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
							if (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(outgoingLink) == bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID) {
								DestroyElementRequest r = new DestroyElementRequest(outgoingLink.getElement(), false);
								cmd.add(new DestroyElementCommand(r));
								cmd.add(new DeleteCommand(getEditingDomain(), outgoingLink));
								continue;
							}
						}
						cmd.add(new DestroyElementCommand(new DestroyElementRequest(getEditingDomain(), cnode.getElement(), false))); // directlyOwned: true
						// don't need explicit deletion of cnode as parent's view deletion would clean child views as well 
						// cmd.add(new org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand(getEditingDomain(), cnode));
						break;
					}
				}
				break;
			}
		}
	}

	/**
	 * @generated
	 */
	protected Command getCreateRelationshipCommand(
			CreateRelationshipRequest req) {
		Command command = req.getTarget() == null ?
				getStartCreateRelationshipCommand(req) : getCompleteCreateRelationshipCommand(req);
		return command != null ? command : super.getCreateRelationshipCommand(req);
	}

	/**
	 * @generated
	 */
	protected Command getStartCreateRelationshipCommand(
			CreateRelationshipRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.InheritanceRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		if (bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AggregationRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		if (bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AssociationRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		return null;
	}

	/**
	 * @generated
	 */
	protected Command getCompleteCreateRelationshipCommand(
			CreateRelationshipRequest req) {
		if (bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.InheritanceRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		if (bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AggregationRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		if (bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003 == req.getElementType()) {
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AssociationRelCreateCommand(req,
					req.getSource(), req.getTarget()));
		}
		return null;
	}

	/**
	 * Returns command to reorient EClass based link. New link target or source
	 * should be the domain model element associated with this node.
	 * 
	 * @generated
	 */
	protected Command getReorientRelationshipCommand(
			ReorientRelationshipRequest req) {
		switch (getVisualID(req)) {
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getGEFWrapper(new bonIDE.diagram.edit.commands.InheritanceRelReorientCommand(req));
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AggregationRelReorientCommand(req));
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getGEFWrapper(new bonIDE.diagram.edit.commands.AssociationRelReorientCommand(req));
		}
		return super.getReorientRelationshipCommand(req);
	}

}

package bonIDE.diagram.edit.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.common.core.command.CommandResult;
import org.eclipse.gmf.runtime.emf.type.core.commands.EditElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;

/**
 * @generated
 */
public class InheritanceRelReorientCommand extends EditElementCommand {

	/**
	 * @generated
	 */
	private final int reorientDirection;

	/**
	 * @generated
	 */
	private final EObject oldEnd;

	/**
	 * @generated
	 */
	private final EObject newEnd;

	/**
	 * @generated
	 */
	public InheritanceRelReorientCommand(ReorientRelationshipRequest request) {
		super(request.getLabel(), request.getRelationship(), request);
		reorientDirection = request.getDirection();
		oldEnd = request.getOldRelationshipEnd();
		newEnd = request.getNewRelationshipEnd();
	}

	/**
	 * @generated
	 */
	public boolean canExecute() {
		if (false == getElementToEdit() instanceof bonIDE.InheritanceRel) {
			return false;
		}
		if (reorientDirection == ReorientRelationshipRequest.REORIENT_SOURCE) {
			return canReorientSource();
		}
		if (reorientDirection == ReorientRelationshipRequest.REORIENT_TARGET) {
			return canReorientTarget();
		}
		return false;
	}

	/**
	 * @generated
	 */
	protected boolean canReorientSource() {
		if (!(oldEnd instanceof bonIDE.Abstraction && newEnd instanceof bonIDE.Abstraction)) {
			return false;
		}
		bonIDE.Abstraction target = getLink().getTarget();
		if (!(getLink().eContainer() instanceof bonIDE.Model)) {
			return false;
		}
		bonIDE.Model container = (bonIDE.Model) getLink().eContainer();
		return bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy.LinkConstraints.canExistInheritanceRel_4001
				(container, getNewSource(), target);
	}

	/**
	 * @generated
	 */
	protected boolean canReorientTarget() {
		if (!(oldEnd instanceof bonIDE.Abstraction && newEnd instanceof bonIDE.Abstraction)) {
			return false;
		}
		bonIDE.Abstraction source = getLink().getSource();
		if (!(getLink().eContainer() instanceof bonIDE.Model)) {
			return false;
		}
		bonIDE.Model container = (bonIDE.Model) getLink().eContainer();
		return bonIDE.diagram.edit.policies.BonideBaseItemSemanticEditPolicy.LinkConstraints.canExistInheritanceRel_4001
				(container, source, getNewTarget());
	}

	/**
	 * @generated
	 */
	protected CommandResult doExecuteWithResult(
			IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		if (!canExecute()) {
			throw new ExecutionException("Invalid arguments in reorient link command"); //$NON-NLS-1$
		}
		if (reorientDirection == ReorientRelationshipRequest.REORIENT_SOURCE) {
			return reorientSource();
		}
		if (reorientDirection == ReorientRelationshipRequest.REORIENT_TARGET) {
			return reorientTarget();
		}
		throw new IllegalStateException();
	}

	/**
	 * @generated
	 */
	protected CommandResult reorientSource() throws ExecutionException {
		getLink().setSource(getNewSource());
		return CommandResult.newOKCommandResult(getLink());
	}

	/**
	 * @generated
	 */
	protected CommandResult reorientTarget() throws ExecutionException {
		getLink().setTarget(getNewTarget());
		return CommandResult.newOKCommandResult(getLink());
	}

	/**
	 * @generated
	 */
	protected bonIDE.InheritanceRel getLink() {
		return (bonIDE.InheritanceRel) getElementToEdit();
	}

	/**
	 * @generated
	 */
	protected bonIDE.Abstraction getOldSource() {
		return (bonIDE.Abstraction) oldEnd;
	}

	/**
	 * @generated
	 */
	protected bonIDE.Abstraction getNewSource() {
		return (bonIDE.Abstraction) newEnd;
	}

	/**
	 * @generated
	 */
	protected bonIDE.Abstraction getOldTarget() {
		return (bonIDE.Abstraction) oldEnd;
	}

	/**
	 * @generated
	 */
	protected bonIDE.Abstraction getNewTarget() {
		return (bonIDE.Abstraction) newEnd;
	}
}

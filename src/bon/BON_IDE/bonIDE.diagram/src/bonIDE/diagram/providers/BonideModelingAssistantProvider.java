package bonIDE.diagram.providers;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.emf.type.core.ElementTypeRegistry;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.ui.services.modelingassistant.ModelingAssistantProvider;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;

/**
 * @generated
 */
public class BonideModelingAssistantProvider extends ModelingAssistantProvider {

	/**
	 * @generated
	 */
	public List getTypesForPopupBar(IAdaptable host) {
		IGraphicalEditPart editPart =
				(IGraphicalEditPart) host.getAdapter(
				IGraphicalEditPart.class);
		if (editPart instanceof bonIDE.diagram.edit.parts.BONClassEditPart) {
			ArrayList types = new ArrayList(4);
			types.add(bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003);
			types.add(bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Feature_3006);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Invariant_3010);
			return types;
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.BONClass2EditPart) {
			ArrayList types = new ArrayList(4);
			types.add(bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003);
			types.add(bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Feature_3006);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Invariant_3010);
			return types;
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.FeatureEditPart) {
			ArrayList types = new ArrayList(3);
			types.add(bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009);
			types.add(bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008);
			types.add(bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007);
			return types;
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart) {
			ArrayList types = new ArrayList(2);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Cluster_3001);
			types.add(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
			return types;
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart) {
			ArrayList types = new ArrayList(2);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Cluster_3001);
			types.add(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002);
			return types;
		}
		if (editPart instanceof bonIDE.diagram.edit.parts.ModelEditPart) {
			ArrayList types = new ArrayList(2);
			types.add(bonIDE.diagram.providers.BonideElementTypes.Cluster_2001);
			types.add(bonIDE.diagram.providers.BonideElementTypes.BONClass_2002);
			return types;
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public List getRelTypesOnSource(IAdaptable source) {
		IGraphicalEditPart sourceEditPart =
				(IGraphicalEditPart) source.getAdapter(
				IGraphicalEditPart.class);
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public List getRelTypesOnTarget(IAdaptable target) {
		IGraphicalEditPart targetEditPart =
				(IGraphicalEditPart) target.getAdapter(
				IGraphicalEditPart.class);
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public List getRelTypesOnSourceAndTarget(
			IAdaptable source, IAdaptable target) {
		IGraphicalEditPart sourceEditPart =
				(IGraphicalEditPart) source.getAdapter(
				IGraphicalEditPart.class);
		IGraphicalEditPart targetEditPart =
				(IGraphicalEditPart) target.getAdapter(
				IGraphicalEditPart.class);
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public List getTypesForSource(IAdaptable target,
			IElementType relationshipType) {
		IGraphicalEditPart targetEditPart =
				(IGraphicalEditPart) target.getAdapter(
				IGraphicalEditPart.class);
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public List getTypesForTarget(IAdaptable source,
			IElementType relationshipType) {
		IGraphicalEditPart sourceEditPart =
				(IGraphicalEditPart) source.getAdapter(
				IGraphicalEditPart.class);
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public EObject selectExistingElementForSource(
			IAdaptable target,
			IElementType relationshipType) {
		return selectExistingElement(target, getTypesForSource(target, relationshipType));
	}

	/**
	 * @generated
	 */
	public EObject selectExistingElementForTarget(
			IAdaptable source,
			IElementType relationshipType) {
		return selectExistingElement(source, getTypesForTarget(source, relationshipType));
	}

	/**
	 * @generated
	 */
	protected EObject selectExistingElement(
			IAdaptable host, Collection types) {
		if (types.isEmpty()) {
			return null;
		}
		IGraphicalEditPart editPart =
				(IGraphicalEditPart) host.getAdapter(
				IGraphicalEditPart.class);
		if (editPart == null) {
			return null;
		}
		Diagram diagram =
				(Diagram) editPart.getRoot().getContents().getModel();
		Collection elements = new HashSet();
		for (Iterator it = diagram.getElement().eAllContents(); it.hasNext();) {
			EObject element = (EObject) it.next();
			if (isApplicableElement(element, types)) {
				elements.add(element);
			}
		}
		if (elements.isEmpty()) {
			return null;
		}
		return selectElement((EObject[]) elements.toArray(
				new EObject[elements.size()]));
	}

	/**
	 * @generated
	 */
	protected boolean isApplicableElement(EObject element, Collection types) {
		IElementType type =
				ElementTypeRegistry.getInstance().getElementType(element);
		return types.contains(type);
	}

	/**
	 * @generated
	 */
	protected EObject selectElement(EObject[] elements) {
		Shell shell = Display.getCurrent().getActiveShell();
		ILabelProvider labelProvider =
				new AdapterFactoryLabelProvider(
				bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getItemProvidersAdapterFactory());
		ElementListSelectionDialog dialog =
				new ElementListSelectionDialog(shell, labelProvider);
		dialog.setMessage(bonIDE.diagram.part.Messages.BonideModelingAssistantProviderMessage);
		dialog.setTitle(bonIDE.diagram.part.Messages.BonideModelingAssistantProviderTitle);
		dialog.setMultipleSelection(false);
		dialog.setElements(elements);
		EObject selected = null;
		if (dialog.open() == Window.OK) {
			selected = (EObject) dialog.getFirstResult();
		}
		return selected;
	}
}

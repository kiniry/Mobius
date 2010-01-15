package bonIDE.diagram.part;

import org.eclipse.core.runtime.Platform;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.View;

/**
 * This registry is used to determine which type of visual object should be
 * created for the corresponding Diagram, Node, ChildNode or Link represented
 * by a domain model object.
 * 
 * @generated
 */
public class BonideVisualIDRegistry {

	/**
	 * @generated
	 */
	private static final String DEBUG_KEY = "bonIDE.diagram/debug/visualID"; //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static int getVisualID(View view) {
		if (view instanceof Diagram) {
			if (bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(view.getType())) {
				return bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID;
			} else {
				return -1;
			}
		}
		return bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view.getType());
	}

	/**
	 * @generated
	 */
	public static String getModelID(View view) {
		View diagram = view.getDiagram();
		while (view != diagram) {
			EAnnotation annotation = view.getEAnnotation("Shortcut"); //$NON-NLS-1$
			if (annotation != null) {
				return (String) annotation.getDetails().get("modelID"); //$NON-NLS-1$
			}
			view = (View) view.eContainer();
		}
		return diagram != null ? diagram.getType() : null;
	}

	/**
	 * @generated
	 */
	public static int getVisualID(String type) {
		try {
			return Integer.parseInt(type);
		} catch (NumberFormatException e) {
			if (Boolean.TRUE.toString().equalsIgnoreCase(Platform.getDebugOption(DEBUG_KEY))) {
				bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError(
						"Unable to parse view type as a visualID number: " + type);
			}
		}
		return -1;
	}

	/**
	 * @generated
	 */
	public static String getType(int visualID) {
		return String.valueOf(visualID);
	}

	/**
	 * @generated
	 */
	public static int getDiagramVisualID(EObject domainElement) {
		if (domainElement == null) {
			return -1;
		}
		if (bonIDE.BonIDEPackage.eINSTANCE.getModel().isSuperTypeOf(domainElement.eClass())
				&& isDiagram((bonIDE.Model) domainElement)) {
			return bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID;
		}
		return -1;
	}

	/**
	 * @generated
	 */
	public static int getNodeVisualID(View containerView, EObject domainElement) {
		if (domainElement == null) {
			return -1;
		}
		String containerModelID = bonIDE.diagram.part.BonideVisualIDRegistry.getModelID(containerView);
		if (!bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(containerModelID)) {
			return -1;
		}
		int containerVisualID;
		if (bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(containerModelID)) {
			containerVisualID = bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(containerView);
		} else {
			if (containerView instanceof Diagram) {
				containerVisualID = bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID;
			} else {
				return -1;
			}
		}
		switch (containerVisualID) {
		case bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID:
			if (bonIDE.BonIDEPackage.eINSTANCE.getCluster().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID;
			}
			if (bonIDE.BonIDEPackage.eINSTANCE.getBONClass().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID;
			}
			break;
		case bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID:
			if (bonIDE.BonIDEPackage.eINSTANCE.getCluster().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID;
			}
			if (bonIDE.BonIDEPackage.eINSTANCE.getBONClass().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID;
			}
			break;
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			if (bonIDE.BonIDEPackage.eINSTANCE.getCluster().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID;
			}
			if (bonIDE.BonIDEPackage.eINSTANCE.getBONClass().isSuperTypeOf(domainElement.eClass())) {
				return bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID;
			}
			break;
		}
		return -1;
	}

	/**
	 * @generated
	 */
	public static boolean canCreateNode(View containerView, int nodeVisualID) {
		String containerModelID = bonIDE.diagram.part.BonideVisualIDRegistry.getModelID(containerView);
		if (!bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(containerModelID)) {
			return false;
		}
		int containerVisualID;
		if (bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(containerModelID)) {
			containerVisualID = bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(containerView);
		} else {
			if (containerView instanceof Diagram) {
				containerVisualID = bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID;
			} else {
				return false;
			}
		}
		switch (containerVisualID) {
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			if (bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.BONClassNameEditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.ClusterName2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			if (bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.BONClassName2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			if (bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			if (bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			if (bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			if (bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID == nodeVisualID) {
				return true;
			}
			break;
		}
		return false;
	}

	/**
	 * @generated
	 */
	public static int getLinkWithClassVisualID(EObject domainElement) {
		if (domainElement == null) {
			return -1;
		}
		return -1;
	}

	/**
	 * User can change implementation of this method to handle some specific
	 * situations not covered by default logic.
	 * 
	 * @generated
	 */
	private static boolean isDiagram(bonIDE.Model element) {
		return true;
	}

}

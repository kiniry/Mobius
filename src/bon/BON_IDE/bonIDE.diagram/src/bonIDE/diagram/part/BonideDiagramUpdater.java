package bonIDE.diagram.part;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.gmf.runtime.notation.View;

/**
 * @generated
 */
public class BonideDiagramUpdater {

	/**
	 * @generated
	 */
	public static List getSemanticChildren(View view) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ClusterClusterCompartmentEditPart.VISUAL_ID:
			return getClusterClusterCompartment_7001SemanticChildren(view);
		case bonIDE.diagram.edit.parts.ClusterClusterCompartment2EditPart.VISUAL_ID:
			return getClusterClusterCompartment_7002SemanticChildren(view);
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			return getModel_1000SemanticChildren(view);
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getClusterClusterCompartment_7001SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Cluster modelElement = (bonIDE.Cluster) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getContents().iterator(); it.hasNext();) {
			bonIDE.StaticAbstraction childElement = (bonIDE.StaticAbstraction) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
			if (visualID == bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getClusterClusterCompartment_7002SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Cluster modelElement = (bonIDE.Cluster) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getContents().iterator(); it.hasNext();) {
			bonIDE.StaticAbstraction childElement = (bonIDE.StaticAbstraction) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
			if (visualID == bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getModel_1000SemanticChildren(View view) {
		if (!view.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Model modelElement = (bonIDE.Model) view.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getAbstractions().iterator(); it.hasNext();) {
			bonIDE.Abstraction childElement = (bonIDE.Abstraction) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
			if (visualID == bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getContainedLinks(View view) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			return getModel_1000ContainedLinks(view);
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getCluster_2001ContainedLinks(view);
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getBONClass_2002ContainedLinks(view);
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getCluster_3001ContainedLinks(view);
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getBONClass_3002ContainedLinks(view);
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getIncomingLinks(View view) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getCluster_2001IncomingLinks(view);
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getBONClass_2002IncomingLinks(view);
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getCluster_3001IncomingLinks(view);
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getBONClass_3002IncomingLinks(view);
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getOutgoingLinks(View view) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getCluster_2001OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getBONClass_2002OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getCluster_3001OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getBONClass_3002OutgoingLinks(view);
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getModel_1000ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_2001ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_2002ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_3001ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_3002ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_2001IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_2002IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_3001IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_3002IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_2001OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_2002OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_3001OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_3002OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

}

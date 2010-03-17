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
		case bonIDE.diagram.edit.parts.BONClassIndexCompartmentEditPart.VISUAL_ID:
			return getBONClassIndexCompartment_7003SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassInheritanceCompartmentEditPart.VISUAL_ID:
			return getBONClassInheritanceCompartment_7005SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassFeatureCompartmentEditPart.VISUAL_ID:
			return getBONClassFeatureCompartment_7007SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassInvariantCompartmentEditPart.VISUAL_ID:
			return getBONClassInvariantCompartment_7012SemanticChildren(view);
		case bonIDE.diagram.edit.parts.FeaturePostConditionCompartmentEditPart.VISUAL_ID:
			return getFeaturePostConditionCompartment_7009SemanticChildren(view);
		case bonIDE.diagram.edit.parts.FeaturePreConditionCompartmentEditPart.VISUAL_ID:
			return getFeaturePreConditionCompartment_7010SemanticChildren(view);
		case bonIDE.diagram.edit.parts.FeatureArgumentCompartmentEditPart.VISUAL_ID:
			return getFeatureArgumentCompartment_7011SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassIndexCompartment2EditPart.VISUAL_ID:
			return getBONClassIndexCompartment_7004SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassInheritanceCompartment2EditPart.VISUAL_ID:
			return getBONClassInheritanceCompartment_7006SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassFeatureCompartment2EditPart.VISUAL_ID:
			return getBONClassFeatureCompartment_7008SemanticChildren(view);
		case bonIDE.diagram.edit.parts.BONClassInvariantCompartment2EditPart.VISUAL_ID:
			return getBONClassInvariantCompartment_7013SemanticChildren(view);
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
	public static List getBONClassIndexCompartment_7003SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getIndexes().iterator(); it.hasNext();) {
			bonIDE.IndexClause childElement = (bonIDE.IndexClause) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassInheritanceCompartment_7005SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		{
			bonIDE.InheritanceClause childElement = modelElement.getParents();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassFeatureCompartment_7007SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getFeatures().iterator(); it.hasNext();) {
			bonIDE.Feature childElement = (bonIDE.Feature) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassInvariantCompartment_7012SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getInvariants().iterator(); it.hasNext();) {
			bonIDE.Invariant childElement = (bonIDE.Invariant) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getFeaturePostConditionCompartment_7009SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Feature modelElement = (bonIDE.Feature) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getPostConditions().iterator(); it.hasNext();) {
			bonIDE.PostCondition childElement = (bonIDE.PostCondition) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getFeaturePreConditionCompartment_7010SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Feature modelElement = (bonIDE.Feature) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getPreConditions().iterator(); it.hasNext();) {
			bonIDE.PreCondition childElement = (bonIDE.PreCondition) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getFeatureArgumentCompartment_7011SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.Feature modelElement = (bonIDE.Feature) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getArguments().iterator(); it.hasNext();) {
			bonIDE.FeatureArgument childElement = (bonIDE.FeatureArgument) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassIndexCompartment_7004SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getIndexes().iterator(); it.hasNext();) {
			bonIDE.IndexClause childElement = (bonIDE.IndexClause) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassInheritanceCompartment_7006SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		{
			bonIDE.InheritanceClause childElement = modelElement.getParents();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassFeatureCompartment_7008SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getFeatures().iterator(); it.hasNext();) {
			bonIDE.Feature childElement = (bonIDE.Feature) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID) {
				result.add(new bonIDE.diagram.part.BonideNodeDescriptor(childElement, visualID));
				continue;
			}
		}
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClassInvariantCompartment_7013SemanticChildren(View view) {
		if (false == view.eContainer() instanceof View) {
			return Collections.EMPTY_LIST;
		}
		View containerView = (View) view.eContainer();
		if (!containerView.isSetElement()) {
			return Collections.EMPTY_LIST;
		}
		bonIDE.BONClass modelElement = (bonIDE.BONClass) containerView.getElement();
		List result = new LinkedList();
		for (Iterator it = modelElement.getInvariants().iterator(); it.hasNext();) {
			bonIDE.Invariant childElement = (bonIDE.Invariant) it.next();
			int visualID = bonIDE.diagram.part.BonideVisualIDRegistry.getNodeVisualID(view, childElement);
			if (visualID == bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID) {
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
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return getIndexClause_3003ContainedLinks(view);
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return getInheritanceClause_3005ContainedLinks(view);
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return getFeature_3006ContainedLinks(view);
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return getFeatureArgument_3007ContainedLinks(view);
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getPreCondition_3008ContainedLinks(view);
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getPostCondition_3009ContainedLinks(view);
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return getInvariant_3010ContainedLinks(view);
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
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return getIndexClause_3003IncomingLinks(view);
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return getInheritanceClause_3005IncomingLinks(view);
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return getFeature_3006IncomingLinks(view);
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return getFeatureArgument_3007IncomingLinks(view);
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getPreCondition_3008IncomingLinks(view);
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getPostCondition_3009IncomingLinks(view);
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return getInvariant_3010IncomingLinks(view);
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
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return getIndexClause_3003OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return getInheritanceClause_3005OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return getFeature_3006OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return getFeatureArgument_3007OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getPreCondition_3008OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getPostCondition_3009OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return getInvariant_3010OutgoingLinks(view);
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
	public static List getIndexClause_3003ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInheritanceClause_3005ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeature_3006ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeatureArgument_3007ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPreCondition_3008ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPostCondition_3009ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInvariant_3010ContainedLinks(View view) {
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
	public static List getIndexClause_3003IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInheritanceClause_3005IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeature_3006IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeatureArgument_3007IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPreCondition_3008IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPostCondition_3009IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInvariant_3010IncomingLinks(View view) {
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

	/**
	 * @generated
	 */
	public static List getIndexClause_3003OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInheritanceClause_3005OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeature_3006OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getFeatureArgument_3007OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPreCondition_3008OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getPostCondition_3009OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getInvariant_3010OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

}

package bonIDE.diagram.part;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import java.util.Map;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.util.EcoreUtil;
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
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getInheritanceRel_4001ContainedLinks(view);
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getAggregationRel_4002ContainedLinks(view);
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getAssociationRel_4003ContainedLinks(view);
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
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getInheritanceRel_4001IncomingLinks(view);
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getAggregationRel_4002IncomingLinks(view);
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getAssociationRel_4003IncomingLinks(view);
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
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getInheritanceRel_4001OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getAggregationRel_4002OutgoingLinks(view);
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getAssociationRel_4003OutgoingLinks(view);
		}
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getModel_1000ContainedLinks(View view) {
		bonIDE.Model modelElement = (bonIDE.Model) view.getElement();
		List result = new LinkedList();
		result.addAll(getContainedTypeModelFacetLinks_InheritanceRel_4001(modelElement));
		result.addAll(getContainedTypeModelFacetLinks_AggregationRel_4002(modelElement));
		result.addAll(getContainedTypeModelFacetLinks_AssociationRel_4003(modelElement));
		return result;
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
	public static List getInheritanceRel_4001ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAggregationRel_4002ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAssociationRel_4003ContainedLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_2001IncomingLinks(View view) {
		bonIDE.Cluster modelElement = (bonIDE.Cluster) view.getElement();
		Map crossReferences = EcoreUtil.CrossReferencer.find(view.eResource().getResourceSet().getResources());
		List result = new LinkedList();
		result.addAll(getIncomingTypeModelFacetLinks_InheritanceRel_4001(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AggregationRel_4002(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AssociationRel_4003(modelElement, crossReferences));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_2002IncomingLinks(View view) {
		bonIDE.BONClass modelElement = (bonIDE.BONClass) view.getElement();
		Map crossReferences = EcoreUtil.CrossReferencer.find(view.eResource().getResourceSet().getResources());
		List result = new LinkedList();
		result.addAll(getIncomingTypeModelFacetLinks_InheritanceRel_4001(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AggregationRel_4002(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AssociationRel_4003(modelElement, crossReferences));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getCluster_3001IncomingLinks(View view) {
		bonIDE.Cluster modelElement = (bonIDE.Cluster) view.getElement();
		Map crossReferences = EcoreUtil.CrossReferencer.find(view.eResource().getResourceSet().getResources());
		List result = new LinkedList();
		result.addAll(getIncomingTypeModelFacetLinks_InheritanceRel_4001(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AggregationRel_4002(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AssociationRel_4003(modelElement, crossReferences));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_3002IncomingLinks(View view) {
		bonIDE.BONClass modelElement = (bonIDE.BONClass) view.getElement();
		Map crossReferences = EcoreUtil.CrossReferencer.find(view.eResource().getResourceSet().getResources());
		List result = new LinkedList();
		result.addAll(getIncomingTypeModelFacetLinks_InheritanceRel_4001(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AggregationRel_4002(modelElement, crossReferences));
		result.addAll(getIncomingTypeModelFacetLinks_AssociationRel_4003(modelElement, crossReferences));
		return result;
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
	public static List getInheritanceRel_4001IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAggregationRel_4002IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAssociationRel_4003IncomingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getCluster_2001OutgoingLinks(View view) {
		bonIDE.Cluster modelElement = (bonIDE.Cluster) view.getElement();
		List result = new LinkedList();
		result.addAll(getOutgoingTypeModelFacetLinks_InheritanceRel_4001(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AggregationRel_4002(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AssociationRel_4003(modelElement));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_2002OutgoingLinks(View view) {
		bonIDE.BONClass modelElement = (bonIDE.BONClass) view.getElement();
		List result = new LinkedList();
		result.addAll(getOutgoingTypeModelFacetLinks_InheritanceRel_4001(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AggregationRel_4002(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AssociationRel_4003(modelElement));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getCluster_3001OutgoingLinks(View view) {
		bonIDE.Cluster modelElement = (bonIDE.Cluster) view.getElement();
		List result = new LinkedList();
		result.addAll(getOutgoingTypeModelFacetLinks_InheritanceRel_4001(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AggregationRel_4002(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AssociationRel_4003(modelElement));
		return result;
	}

	/**
	 * @generated
	 */
	public static List getBONClass_3002OutgoingLinks(View view) {
		bonIDE.BONClass modelElement = (bonIDE.BONClass) view.getElement();
		List result = new LinkedList();
		result.addAll(getOutgoingTypeModelFacetLinks_InheritanceRel_4001(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AggregationRel_4002(modelElement));
		result.addAll(getOutgoingTypeModelFacetLinks_AssociationRel_4003(modelElement));
		return result;
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

	/**
	 * @generated
	 */
	public static List getInheritanceRel_4001OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAggregationRel_4002OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	public static List getAssociationRel_4003OutgoingLinks(View view) {
		return Collections.EMPTY_LIST;
	}

	/**
	 * @generated
	 */
	private static Collection getContainedTypeModelFacetLinks_InheritanceRel_4001(bonIDE.Model container) {
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.InheritanceRel) {
				continue;
			}
			bonIDE.InheritanceRel link = (bonIDE.InheritanceRel) linkObject;
			if (bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001,
					bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getContainedTypeModelFacetLinks_AggregationRel_4002(bonIDE.Model container) {
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.AggregationRel) {
				continue;
			}
			bonIDE.AggregationRel link = (bonIDE.AggregationRel) linkObject;
			if (bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002,
					bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getContainedTypeModelFacetLinks_AssociationRel_4003(bonIDE.Model container) {
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.AssociationRel) {
				continue;
			}
			bonIDE.AssociationRel link = (bonIDE.AssociationRel) linkObject;
			if (bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003,
					bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getIncomingTypeModelFacetLinks_InheritanceRel_4001(bonIDE.Abstraction target, Map crossReferences) {
		Collection result = new LinkedList();
		Collection settings = (Collection) crossReferences.get(target);
		for (Iterator it = settings.iterator(); it.hasNext();) {
			EStructuralFeature.Setting setting = (EStructuralFeature.Setting) it.next();
			if (setting.getEStructuralFeature() != bonIDE.BonIDEPackage.eINSTANCE.getStaticRelationship_Target()
					|| false == setting.getEObject() instanceof bonIDE.InheritanceRel) {
				continue;
			}
			bonIDE.InheritanceRel link = (bonIDE.InheritanceRel) setting.getEObject();
			if (bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, target, link,
					bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001, bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getIncomingTypeModelFacetLinks_AggregationRel_4002(bonIDE.Abstraction target, Map crossReferences) {
		Collection result = new LinkedList();
		Collection settings = (Collection) crossReferences.get(target);
		for (Iterator it = settings.iterator(); it.hasNext();) {
			EStructuralFeature.Setting setting = (EStructuralFeature.Setting) it.next();
			if (setting.getEStructuralFeature() != bonIDE.BonIDEPackage.eINSTANCE.getStaticRelationship_Target()
					|| false == setting.getEObject() instanceof bonIDE.AggregationRel) {
				continue;
			}
			bonIDE.AggregationRel link = (bonIDE.AggregationRel) setting.getEObject();
			if (bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, target, link,
					bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002, bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getIncomingTypeModelFacetLinks_AssociationRel_4003(bonIDE.Abstraction target, Map crossReferences) {
		Collection result = new LinkedList();
		Collection settings = (Collection) crossReferences.get(target);
		for (Iterator it = settings.iterator(); it.hasNext();) {
			EStructuralFeature.Setting setting = (EStructuralFeature.Setting) it.next();
			if (setting.getEStructuralFeature() != bonIDE.BonIDEPackage.eINSTANCE.getStaticRelationship_Target()
					|| false == setting.getEObject() instanceof bonIDE.AssociationRel) {
				continue;
			}
			bonIDE.AssociationRel link = (bonIDE.AssociationRel) setting.getEObject();
			if (bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction src = link.getSource();
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, target, link,
					bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003, bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getOutgoingTypeModelFacetLinks_InheritanceRel_4001(bonIDE.Abstraction source) {
		bonIDE.Model container = null;
		// Find container element for the link.
		// Climb up by containment hierarchy starting from the source
		// and return the first element that is instance of the container class.
		for (EObject element = source; element != null && container == null; element = element.eContainer()) {
			if (element instanceof bonIDE.Model) {
				container = (bonIDE.Model) element;
			}
		}
		if (container == null) {
			return Collections.EMPTY_LIST;
		}
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.InheritanceRel) {
				continue;
			}
			bonIDE.InheritanceRel link = (bonIDE.InheritanceRel) linkObject;
			if (bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			if (src != source) {
				continue;
			}
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001,
					bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getOutgoingTypeModelFacetLinks_AggregationRel_4002(bonIDE.Abstraction source) {
		bonIDE.Model container = null;
		// Find container element for the link.
		// Climb up by containment hierarchy starting from the source
		// and return the first element that is instance of the container class.
		for (EObject element = source; element != null && container == null; element = element.eContainer()) {
			if (element instanceof bonIDE.Model) {
				container = (bonIDE.Model) element;
			}
		}
		if (container == null) {
			return Collections.EMPTY_LIST;
		}
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.AggregationRel) {
				continue;
			}
			bonIDE.AggregationRel link = (bonIDE.AggregationRel) linkObject;
			if (bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			if (src != source) {
				continue;
			}
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002,
					bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID));
		}
		return result;
	}

	/**
	 * @generated
	 */
	private static Collection getOutgoingTypeModelFacetLinks_AssociationRel_4003(bonIDE.Abstraction source) {
		bonIDE.Model container = null;
		// Find container element for the link.
		// Climb up by containment hierarchy starting from the source
		// and return the first element that is instance of the container class.
		for (EObject element = source; element != null && container == null; element = element.eContainer()) {
			if (element instanceof bonIDE.Model) {
				container = (bonIDE.Model) element;
			}
		}
		if (container == null) {
			return Collections.EMPTY_LIST;
		}
		Collection result = new LinkedList();
		for (Iterator links = container.getRelationships().iterator(); links.hasNext();) {
			EObject linkObject = (EObject) links.next();
			if (false == linkObject instanceof bonIDE.AssociationRel) {
				continue;
			}
			bonIDE.AssociationRel link = (bonIDE.AssociationRel) linkObject;
			if (bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID != bonIDE.diagram.part.BonideVisualIDRegistry
					.getLinkWithClassVisualID(link)) {
				continue;
			}
			bonIDE.Abstraction dst = link.getTarget();
			bonIDE.Abstraction src = link.getSource();
			if (src != source) {
				continue;
			}
			result.add(new bonIDE.diagram.part.BonideLinkDescriptor(src, dst, link, bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003,
					bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID));
		}
		return result;
	}

}

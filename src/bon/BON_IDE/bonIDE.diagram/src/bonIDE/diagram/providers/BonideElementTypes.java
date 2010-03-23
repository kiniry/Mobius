package bonIDE.diagram.providers;

import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.ENamedElement;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.gmf.runtime.emf.type.core.ElementTypeRegistry;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;

/**
 * @generated
 */
public class BonideElementTypes extends ElementInitializers {

	/**
	 * @generated
	 */
	private BonideElementTypes() {
	}

	/**
	 * @generated
	 */
	private static Map elements;

	/**
	 * @generated
	 */
	private static ImageRegistry imageRegistry;

	/**
	 * @generated
	 */
	private static Set KNOWN_ELEMENT_TYPES;

	/**
	 * @generated
	 */
	public static final IElementType Model_1000 = getElementType("bonIDE.diagram.Model_1000"); //$NON-NLS-1$
	/**
	 * @generated
	 */
	public static final IElementType Cluster_2001 = getElementType("bonIDE.diagram.Cluster_2001"); //$NON-NLS-1$
	/**
	 * @generated
	 */
	public static final IElementType BONClass_2002 = getElementType("bonIDE.diagram.BONClass_2002"); //$NON-NLS-1$
	/**
	 * @generated
	 */
	public static final IElementType Cluster_3001 = getElementType("bonIDE.diagram.Cluster_3001"); //$NON-NLS-1$
	/**
	 * @generated
	 */
	public static final IElementType BONClass_3002 = getElementType("bonIDE.diagram.BONClass_3002"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType IndexClause_3003 = getElementType("bonIDE.diagram.IndexClause_3003"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType InheritanceClause_3005 = getElementType("bonIDE.diagram.InheritanceClause_3005"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType Feature_3006 = getElementType("bonIDE.diagram.Feature_3006"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType FeatureArgument_3007 = getElementType("bonIDE.diagram.FeatureArgument_3007"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType PreCondition_3008 = getElementType("bonIDE.diagram.PreCondition_3008"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType PostCondition_3009 = getElementType("bonIDE.diagram.PostCondition_3009"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType Invariant_3010 = getElementType("bonIDE.diagram.Invariant_3010"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType InheritanceRel_4001 = getElementType("bonIDE.diagram.InheritanceRel_4001"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType AggregationRel_4002 = getElementType("bonIDE.diagram.AggregationRel_4002"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	public static final IElementType AssociationRel_4003 = getElementType("bonIDE.diagram.AssociationRel_4003"); //$NON-NLS-1$

	/**
	 * @generated
	 */
	private static ImageRegistry getImageRegistry() {
		if (imageRegistry == null) {
			imageRegistry = new ImageRegistry();
		}
		return imageRegistry;
	}

	/**
	 * @generated
	 */
	private static String getImageRegistryKey(ENamedElement element) {
		return element.getName();
	}

	/**
	 * @generated
	 */
	private static ImageDescriptor getProvidedImageDescriptor(ENamedElement element) {
		if (element instanceof EStructuralFeature) {
			EStructuralFeature feature = ((EStructuralFeature) element);
			EClass eContainingClass = feature.getEContainingClass();
			EClassifier eType = feature.getEType();
			if (eContainingClass != null && !eContainingClass.isAbstract()) {
				element = eContainingClass;
			} else if (eType instanceof EClass && !((EClass) eType).isAbstract()) {
				element = eType;
			}
		}
		if (element instanceof EClass) {
			EClass eClass = (EClass) element;
			if (!eClass.isAbstract()) {
				return bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getItemImageDescriptor(
						eClass.getEPackage().getEFactoryInstance().create(eClass));
			}
		}
		// TODO : support structural features
		return null;
	}

	/**
	 * @generated
	 */
	public static ImageDescriptor getImageDescriptor(ENamedElement element) {
		String key = getImageRegistryKey(element);
		ImageDescriptor imageDescriptor = getImageRegistry().getDescriptor(key);
		if (imageDescriptor == null) {
			imageDescriptor = getProvidedImageDescriptor(element);
			if (imageDescriptor == null) {
				imageDescriptor = ImageDescriptor.getMissingImageDescriptor();
			}
			getImageRegistry().put(key, imageDescriptor);
		}
		return imageDescriptor;
	}

	/**
	 * @generated
	 */
	public static Image getImage(ENamedElement element) {
		String key = getImageRegistryKey(element);
		Image image = getImageRegistry().get(key);
		if (image == null) {
			ImageDescriptor imageDescriptor = getProvidedImageDescriptor(element);
			if (imageDescriptor == null) {
				imageDescriptor = ImageDescriptor.getMissingImageDescriptor();
			}
			getImageRegistry().put(key, imageDescriptor);
			image = getImageRegistry().get(key);
		}
		return image;
	}

	/**
	 * @generated
	 */
	public static ImageDescriptor getImageDescriptor(IAdaptable hint) {
		ENamedElement element = getElement(hint);
		if (element == null) {
			return null;
		}
		return getImageDescriptor(element);
	}

	/**
	 * @generated
	 */
	public static Image getImage(IAdaptable hint) {
		ENamedElement element = getElement(hint);
		if (element == null) {
			return null;
		}
		return getImage(element);
	}

	/**
	 * Returns 'type' of the ecore object associated with the hint.
	 * 
	 * @generated
	 */
	public static ENamedElement getElement(IAdaptable hint) {
		Object type = hint.getAdapter(IElementType.class);
		if (elements == null) {
			elements = new IdentityHashMap();

			elements.put(Model_1000, bonIDE.BonIDEPackage.eINSTANCE.getModel());

			elements.put(Cluster_2001, bonIDE.BonIDEPackage.eINSTANCE.getCluster());

			elements.put(BONClass_2002, bonIDE.BonIDEPackage.eINSTANCE.getBONClass());

			elements.put(Cluster_3001, bonIDE.BonIDEPackage.eINSTANCE.getCluster());

			elements.put(BONClass_3002, bonIDE.BonIDEPackage.eINSTANCE.getBONClass());

			elements.put(IndexClause_3003, bonIDE.BonIDEPackage.eINSTANCE.getIndexClause());

			elements.put(InheritanceClause_3005, bonIDE.BonIDEPackage.eINSTANCE.getInheritanceClause());

			elements.put(Feature_3006, bonIDE.BonIDEPackage.eINSTANCE.getFeature());

			elements.put(FeatureArgument_3007, bonIDE.BonIDEPackage.eINSTANCE.getFeatureArgument());

			elements.put(PreCondition_3008, bonIDE.BonIDEPackage.eINSTANCE.getPreCondition());

			elements.put(PostCondition_3009, bonIDE.BonIDEPackage.eINSTANCE.getPostCondition());

			elements.put(Invariant_3010, bonIDE.BonIDEPackage.eINSTANCE.getInvariant());

			elements.put(InheritanceRel_4001, bonIDE.BonIDEPackage.eINSTANCE.getInheritanceRel());

			elements.put(AggregationRel_4002, bonIDE.BonIDEPackage.eINSTANCE.getAggregationRel());

			elements.put(AssociationRel_4003, bonIDE.BonIDEPackage.eINSTANCE.getAssociationRel());
		}
		return (ENamedElement) elements.get(type);
	}

	/**
	 * @generated
	 */
	private static IElementType getElementType(String id) {
		return ElementTypeRegistry.getInstance().getType(id);
	}

	/**
	 * @generated
	 */
	public static boolean isKnownElementType(IElementType elementType) {
		if (KNOWN_ELEMENT_TYPES == null) {
			KNOWN_ELEMENT_TYPES = new HashSet();
			KNOWN_ELEMENT_TYPES.add(Model_1000);
			KNOWN_ELEMENT_TYPES.add(Cluster_2001);
			KNOWN_ELEMENT_TYPES.add(BONClass_2002);
			KNOWN_ELEMENT_TYPES.add(Cluster_3001);
			KNOWN_ELEMENT_TYPES.add(BONClass_3002);
			KNOWN_ELEMENT_TYPES.add(IndexClause_3003);
			KNOWN_ELEMENT_TYPES.add(InheritanceClause_3005);
			KNOWN_ELEMENT_TYPES.add(Feature_3006);
			KNOWN_ELEMENT_TYPES.add(FeatureArgument_3007);
			KNOWN_ELEMENT_TYPES.add(PreCondition_3008);
			KNOWN_ELEMENT_TYPES.add(PostCondition_3009);
			KNOWN_ELEMENT_TYPES.add(Invariant_3010);
			KNOWN_ELEMENT_TYPES.add(InheritanceRel_4001);
			KNOWN_ELEMENT_TYPES.add(AggregationRel_4002);
			KNOWN_ELEMENT_TYPES.add(AssociationRel_4003);
		}
		return KNOWN_ELEMENT_TYPES.contains(elementType);
	}

	/**
	 * @generated
	 */
	public static IElementType getElementType(int visualID) {
		switch (visualID) {
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			return Model_1000;
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return Cluster_2001;
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return BONClass_2002;
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return Cluster_3001;
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return BONClass_3002;
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return IndexClause_3003;
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return InheritanceClause_3005;
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return Feature_3006;
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return FeatureArgument_3007;
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return PreCondition_3008;
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return PostCondition_3009;
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return Invariant_3010;
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return InheritanceRel_4001;
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return AggregationRel_4002;
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return AssociationRel_4003;
		}
		return null;
	}

}

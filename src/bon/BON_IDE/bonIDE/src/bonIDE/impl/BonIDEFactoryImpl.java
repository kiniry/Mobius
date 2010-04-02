/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.impl;

import bonIDE.*;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class BonIDEFactoryImpl extends EFactoryImpl implements BonIDEFactory {
	/**
	 * Creates the default factory implementation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static BonIDEFactory init() {
		try {
			BonIDEFactory theBonIDEFactory = (BonIDEFactory)EPackage.Registry.INSTANCE.getEFactory("http://www.ucd.ie/bonIDE"); 
			if (theBonIDEFactory != null) {
				return theBonIDEFactory;
			}
		}
		catch (Exception exception) {
			EcorePlugin.INSTANCE.log(exception);
		}
		return new BonIDEFactoryImpl();
	}

	/**
	 * Creates an instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BonIDEFactoryImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EObject create(EClass eClass) {
		switch (eClass.getClassifierID()) {
			case BonIDEPackage.MODEL: return createModel();
			case BonIDEPackage.CLUSTER: return createCluster();
			case BonIDEPackage.BON_CLASS: return createBONClass();
			case BonIDEPackage.FEATURE: return createFeature();
			case BonIDEPackage.INDEX_CLAUSE: return createIndexClause();
			case BonIDEPackage.INHERITANCE_CLAUSE: return createInheritanceClause();
			case BonIDEPackage.FEATURE_ARGUMENT: return createFeatureArgument();
			case BonIDEPackage.PRE_CONDITION: return createPreCondition();
			case BonIDEPackage.POST_CONDITION: return createPostCondition();
			case BonIDEPackage.INVARIANT: return createInvariant();
			case BonIDEPackage.STATIC_RELATIONSHIP: return createStaticRelationship();
			case BonIDEPackage.INHERITANCE_REL: return createInheritanceRel();
			case BonIDEPackage.CLIENT_SUPPLIER_REL: return createClientSupplierRel();
			case BonIDEPackage.AGGREGATION_REL: return createAggregationRel();
			case BonIDEPackage.ASSOCIATION_REL: return createAssociationRel();
			default:
				throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object createFromString(EDataType eDataType, String initialValue) {
		switch (eDataType.getClassifierID()) {
			case BonIDEPackage.IMPLEMENTATION_STATUS:
				return createImplementationStatusFromString(eDataType, initialValue);
			case BonIDEPackage.RELATIONSHIP_TYPE:
				return createRelationshipTypeFromString(eDataType, initialValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String convertToString(EDataType eDataType, Object instanceValue) {
		switch (eDataType.getClassifierID()) {
			case BonIDEPackage.IMPLEMENTATION_STATUS:
				return convertImplementationStatusToString(eDataType, instanceValue);
			case BonIDEPackage.RELATIONSHIP_TYPE:
				return convertRelationshipTypeToString(eDataType, instanceValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Model createModel() {
		ModelImpl model = new ModelImpl();
		return model;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Cluster createCluster() {
		ClusterImpl cluster = new ClusterImpl();
		return cluster;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BONClass createBONClass() {
		BONClassImpl bonClass = new BONClassImpl();
		return bonClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Feature createFeature() {
		FeatureImpl feature = new FeatureImpl();
		return feature;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IndexClause createIndexClause() {
		IndexClauseImpl indexClause = new IndexClauseImpl();
		return indexClause;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InheritanceClause createInheritanceClause() {
		InheritanceClauseImpl inheritanceClause = new InheritanceClauseImpl();
		return inheritanceClause;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public FeatureArgument createFeatureArgument() {
		FeatureArgumentImpl featureArgument = new FeatureArgumentImpl();
		return featureArgument;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PreCondition createPreCondition() {
		PreConditionImpl preCondition = new PreConditionImpl();
		return preCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PostCondition createPostCondition() {
		PostConditionImpl postCondition = new PostConditionImpl();
		return postCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Invariant createInvariant() {
		InvariantImpl invariant = new InvariantImpl();
		return invariant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public StaticRelationship createStaticRelationship() {
		StaticRelationshipImpl staticRelationship = new StaticRelationshipImpl();
		return staticRelationship;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InheritanceRel createInheritanceRel() {
		InheritanceRelImpl inheritanceRel = new InheritanceRelImpl();
		return inheritanceRel;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ClientSupplierRel createClientSupplierRel() {
		ClientSupplierRelImpl clientSupplierRel = new ClientSupplierRelImpl();
		return clientSupplierRel;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AggregationRel createAggregationRel() {
		AggregationRelImpl aggregationRel = new AggregationRelImpl();
		return aggregationRel;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AssociationRel createAssociationRel() {
		AssociationRelImpl associationRel = new AssociationRelImpl();
		return associationRel;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ImplementationStatus createImplementationStatusFromString(EDataType eDataType, String initialValue) {
		ImplementationStatus result = ImplementationStatus.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertImplementationStatusToString(EDataType eDataType, Object instanceValue) {
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RelationshipType createRelationshipTypeFromString(EDataType eDataType, String initialValue) {
		RelationshipType result = RelationshipType.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertRelationshipTypeToString(EDataType eDataType, Object instanceValue) {
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BonIDEPackage getBonIDEPackage() {
		return (BonIDEPackage)getEPackage();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @deprecated
	 * @generated
	 */
	@Deprecated
	public static BonIDEPackage getPackage() {
		return BonIDEPackage.eINSTANCE;
	}

} //BonIDEFactoryImpl

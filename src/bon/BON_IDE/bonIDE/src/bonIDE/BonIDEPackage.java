/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see bonIDE.BonIDEFactory
 * @model kind="package"
 * @generated
 */
public interface BonIDEPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "bonIDE";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "http://www.ucd.ie/bonIDE";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "bonIDE";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	BonIDEPackage eINSTANCE = bonIDE.impl.BonIDEPackageImpl.init();

	/**
	 * The meta object id for the '{@link bonIDE.impl.ModelImpl <em>Model</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.ModelImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getModel()
	 * @generated
	 */
	int MODEL = 0;

	/**
	 * The feature id for the '<em><b>Abstractions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__ABSTRACTIONS = 0;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__RELATIONSHIPS = 1;

	/**
	 * The number of structural features of the '<em>Model</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link bonIDE.impl.AbstractionImpl <em>Abstraction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.AbstractionImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getAbstraction()
	 * @generated
	 */
	int ABSTRACTION = 1;

	/**
	 * The number of structural features of the '<em>Abstraction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACTION_FEATURE_COUNT = 0;

	/**
	 * The meta object id for the '{@link bonIDE.impl.StaticAbstractionImpl <em>Static Abstraction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.StaticAbstractionImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getStaticAbstraction()
	 * @generated
	 */
	int STATIC_ABSTRACTION = 4;

	/**
	 * The number of structural features of the '<em>Static Abstraction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_ABSTRACTION_FEATURE_COUNT = ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link bonIDE.impl.ClusterImpl <em>Cluster</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.ClusterImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getCluster()
	 * @generated
	 */
	int CLUSTER = 2;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__CONTENTS = STATIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__NAME = STATIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Collapsed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__COLLAPSED = STATIC_ABSTRACTION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Expanded Height</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__EXPANDED_HEIGHT = STATIC_ABSTRACTION_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Cluster</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER_FEATURE_COUNT = STATIC_ABSTRACTION_FEATURE_COUNT + 4;

	/**
	 * The meta object id for the '{@link bonIDE.impl.BONClassImpl <em>BON Class</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.BONClassImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getBONClass()
	 * @generated
	 */
	int BON_CLASS = 3;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__NAME = STATIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Features</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__FEATURES = STATIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__IS_DEFERRED = STATIC_ABSTRACTION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Implementation Status</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__IMPLEMENTATION_STATUS = STATIC_ABSTRACTION_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Indexes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__INDEXES = STATIC_ABSTRACTION_FEATURE_COUNT + 4;

	/**
	 * The feature id for the '<em><b>Parents</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__PARENTS = STATIC_ABSTRACTION_FEATURE_COUNT + 5;

	/**
	 * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__INVARIANTS = STATIC_ABSTRACTION_FEATURE_COUNT + 6;

	/**
	 * The number of structural features of the '<em>BON Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS_FEATURE_COUNT = STATIC_ABSTRACTION_FEATURE_COUNT + 7;

	/**
	 * The meta object id for the '{@link bonIDE.impl.FeatureImpl <em>Feature</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.FeatureImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getFeature()
	 * @generated
	 */
	int FEATURE = 5;

	/**
	 * The feature id for the '<em><b>Names</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__NAMES = 0;

	/**
	 * The feature id for the '<em><b>Modifier</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__MODIFIER = 1;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__TYPE = 2;

	/**
	 * The feature id for the '<em><b>Comment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__COMMENT = 3;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__ARGUMENTS = 4;

	/**
	 * The feature id for the '<em><b>Post Conditions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__POST_CONDITIONS = 5;

	/**
	 * The feature id for the '<em><b>Pre Conditions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__PRE_CONDITIONS = 6;

	/**
	 * The number of structural features of the '<em>Feature</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_FEATURE_COUNT = 7;


	/**
	 * The meta object id for the '{@link bonIDE.impl.IndexClauseImpl <em>Index Clause</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.IndexClauseImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getIndexClause()
	 * @generated
	 */
	int INDEX_CLAUSE = 6;

	/**
	 * The feature id for the '<em><b>Identifier</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEX_CLAUSE__IDENTIFIER = 0;

	/**
	 * The feature id for the '<em><b>Terms</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEX_CLAUSE__TERMS = 1;

	/**
	 * The number of structural features of the '<em>Index Clause</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INDEX_CLAUSE_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link bonIDE.impl.InheritanceClauseImpl <em>Inheritance Clause</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.InheritanceClauseImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getInheritanceClause()
	 * @generated
	 */
	int INHERITANCE_CLAUSE = 7;

	/**
	 * The feature id for the '<em><b>Parent Names</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_CLAUSE__PARENT_NAMES = 0;

	/**
	 * The number of structural features of the '<em>Inheritance Clause</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_CLAUSE_FEATURE_COUNT = 1;

	/**
	 * The meta object id for the '{@link bonIDE.impl.FeatureArgumentImpl <em>Feature Argument</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.FeatureArgumentImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getFeatureArgument()
	 * @generated
	 */
	int FEATURE_ARGUMENT = 8;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_ARGUMENT__NAME = 0;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_ARGUMENT__TYPE = 1;

	/**
	 * The feature id for the '<em><b>Container Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_ARGUMENT__CONTAINER_TYPE = 2;

	/**
	 * The number of structural features of the '<em>Feature Argument</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_ARGUMENT_FEATURE_COUNT = 3;

	/**
	 * The meta object id for the '{@link bonIDE.impl.PreConditionImpl <em>Pre Condition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.PreConditionImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getPreCondition()
	 * @generated
	 */
	int PRE_CONDITION = 9;

	/**
	 * The feature id for the '<em><b>Content</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRE_CONDITION__CONTENT = 0;

	/**
	 * The number of structural features of the '<em>Pre Condition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRE_CONDITION_FEATURE_COUNT = 1;

	/**
	 * The meta object id for the '{@link bonIDE.impl.PostConditionImpl <em>Post Condition</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.PostConditionImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getPostCondition()
	 * @generated
	 */
	int POST_CONDITION = 10;

	/**
	 * The feature id for the '<em><b>Content</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int POST_CONDITION__CONTENT = 0;

	/**
	 * The number of structural features of the '<em>Post Condition</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int POST_CONDITION_FEATURE_COUNT = 1;

	/**
	 * The meta object id for the '{@link bonIDE.impl.InvariantImpl <em>Invariant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.InvariantImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getInvariant()
	 * @generated
	 */
	int INVARIANT = 11;

	/**
	 * The feature id for the '<em><b>Content</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INVARIANT__CONTENT = 0;

	/**
	 * The number of structural features of the '<em>Invariant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INVARIANT_FEATURE_COUNT = 1;

	/**
	 * The meta object id for the '{@link bonIDE.impl.StaticRelationshipImpl <em>Static Relationship</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.StaticRelationshipImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getStaticRelationship()
	 * @generated
	 */
	int STATIC_RELATIONSHIP = 12;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP__TYPE = 0;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP__SOURCE = 1;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP__TARGET = 2;

	/**
	 * The number of structural features of the '<em>Static Relationship</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP_FEATURE_COUNT = 3;

	/**
	 * The meta object id for the '{@link bonIDE.impl.InheritanceRelImpl <em>Inheritance Rel</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.InheritanceRelImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getInheritanceRel()
	 * @generated
	 */
	int INHERITANCE_REL = 13;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_REL__TYPE = STATIC_RELATIONSHIP__TYPE;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_REL__SOURCE = STATIC_RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_REL__TARGET = STATIC_RELATIONSHIP__TARGET;

	/**
	 * The number of structural features of the '<em>Inheritance Rel</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_REL_FEATURE_COUNT = STATIC_RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link bonIDE.impl.ClientSupplierRelImpl <em>Client Supplier Rel</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.ClientSupplierRelImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getClientSupplierRel()
	 * @generated
	 */
	int CLIENT_SUPPLIER_REL = 14;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_REL__TYPE = STATIC_RELATIONSHIP__TYPE;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_REL__SOURCE = STATIC_RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_REL__TARGET = STATIC_RELATIONSHIP__TARGET;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_REL__NAME = STATIC_RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Client Supplier Rel</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_REL_FEATURE_COUNT = STATIC_RELATIONSHIP_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link bonIDE.impl.AggregationRelImpl <em>Aggregation Rel</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.AggregationRelImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getAggregationRel()
	 * @generated
	 */
	int AGGREGATION_REL = 15;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_REL__TYPE = CLIENT_SUPPLIER_REL__TYPE;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_REL__SOURCE = CLIENT_SUPPLIER_REL__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_REL__TARGET = CLIENT_SUPPLIER_REL__TARGET;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_REL__NAME = CLIENT_SUPPLIER_REL__NAME;

	/**
	 * The number of structural features of the '<em>Aggregation Rel</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_REL_FEATURE_COUNT = CLIENT_SUPPLIER_REL_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link bonIDE.impl.AssociationRelImpl <em>Association Rel</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.impl.AssociationRelImpl
	 * @see bonIDE.impl.BonIDEPackageImpl#getAssociationRel()
	 * @generated
	 */
	int ASSOCIATION_REL = 16;

	/**
	 * The feature id for the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_REL__TYPE = CLIENT_SUPPLIER_REL__TYPE;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_REL__SOURCE = CLIENT_SUPPLIER_REL__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_REL__TARGET = CLIENT_SUPPLIER_REL__TARGET;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_REL__NAME = CLIENT_SUPPLIER_REL__NAME;

	/**
	 * The number of structural features of the '<em>Association Rel</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_REL_FEATURE_COUNT = CLIENT_SUPPLIER_REL_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link bonIDE.ImplementationStatus <em>Implementation Status</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.ImplementationStatus
	 * @see bonIDE.impl.BonIDEPackageImpl#getImplementationStatus()
	 * @generated
	 */
	int IMPLEMENTATION_STATUS = 17;


	/**
	 * The meta object id for the '{@link bonIDE.RelationshipType <em>Relationship Type</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see bonIDE.RelationshipType
	 * @see bonIDE.impl.BonIDEPackageImpl#getRelationshipType()
	 * @generated
	 */
	int RELATIONSHIP_TYPE = 18;


	/**
	 * Returns the meta object for class '{@link bonIDE.Model <em>Model</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Model</em>'.
	 * @see bonIDE.Model
	 * @generated
	 */
	EClass getModel();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Model#getAbstractions <em>Abstractions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Abstractions</em>'.
	 * @see bonIDE.Model#getAbstractions()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Abstractions();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Model#getRelationships <em>Relationships</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Relationships</em>'.
	 * @see bonIDE.Model#getRelationships()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Relationships();

	/**
	 * Returns the meta object for class '{@link bonIDE.Abstraction <em>Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Abstraction</em>'.
	 * @see bonIDE.Abstraction
	 * @generated
	 */
	EClass getAbstraction();

	/**
	 * Returns the meta object for class '{@link bonIDE.Cluster <em>Cluster</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Cluster</em>'.
	 * @see bonIDE.Cluster
	 * @generated
	 */
	EClass getCluster();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Cluster#getContents <em>Contents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Contents</em>'.
	 * @see bonIDE.Cluster#getContents()
	 * @see #getCluster()
	 * @generated
	 */
	EReference getCluster_Contents();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Cluster#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see bonIDE.Cluster#getName()
	 * @see #getCluster()
	 * @generated
	 */
	EAttribute getCluster_Name();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Cluster#isCollapsed <em>Collapsed</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Collapsed</em>'.
	 * @see bonIDE.Cluster#isCollapsed()
	 * @see #getCluster()
	 * @generated
	 */
	EAttribute getCluster_Collapsed();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Cluster#getExpandedHeight <em>Expanded Height</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Expanded Height</em>'.
	 * @see bonIDE.Cluster#getExpandedHeight()
	 * @see #getCluster()
	 * @generated
	 */
	EAttribute getCluster_ExpandedHeight();

	/**
	 * Returns the meta object for class '{@link bonIDE.BONClass <em>BON Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>BON Class</em>'.
	 * @see bonIDE.BONClass
	 * @generated
	 */
	EClass getBONClass();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.BONClass#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see bonIDE.BONClass#getName()
	 * @see #getBONClass()
	 * @generated
	 */
	EAttribute getBONClass_Name();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.BONClass#getFeatures <em>Features</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Features</em>'.
	 * @see bonIDE.BONClass#getFeatures()
	 * @see #getBONClass()
	 * @generated
	 */
	EReference getBONClass_Features();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.BONClass#isIsDeferred <em>Is Deferred</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Deferred</em>'.
	 * @see bonIDE.BONClass#isIsDeferred()
	 * @see #getBONClass()
	 * @generated
	 */
	EAttribute getBONClass_IsDeferred();

	/**
	 * Returns the meta object for the containment reference '{@link bonIDE.BONClass#getParents <em>Parents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Parents</em>'.
	 * @see bonIDE.BONClass#getParents()
	 * @see #getBONClass()
	 * @generated
	 */
	EReference getBONClass_Parents();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.BONClass#getInvariants <em>Invariants</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Invariants</em>'.
	 * @see bonIDE.BONClass#getInvariants()
	 * @see #getBONClass()
	 * @generated
	 */
	EReference getBONClass_Invariants();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.BONClass#getIndexes <em>Indexes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Indexes</em>'.
	 * @see bonIDE.BONClass#getIndexes()
	 * @see #getBONClass()
	 * @generated
	 */
	EReference getBONClass_Indexes();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.BONClass#getImplementationStatus <em>Implementation Status</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Implementation Status</em>'.
	 * @see bonIDE.BONClass#getImplementationStatus()
	 * @see #getBONClass()
	 * @generated
	 */
	EAttribute getBONClass_ImplementationStatus();

	/**
	 * Returns the meta object for class '{@link bonIDE.StaticAbstraction <em>Static Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Static Abstraction</em>'.
	 * @see bonIDE.StaticAbstraction
	 * @generated
	 */
	EClass getStaticAbstraction();

	/**
	 * Returns the meta object for class '{@link bonIDE.Feature <em>Feature</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Feature</em>'.
	 * @see bonIDE.Feature
	 * @generated
	 */
	EClass getFeature();

	/**
	 * Returns the meta object for the attribute list '{@link bonIDE.Feature#getNames <em>Names</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Names</em>'.
	 * @see bonIDE.Feature#getNames()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Names();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Feature#getModifier <em>Modifier</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Modifier</em>'.
	 * @see bonIDE.Feature#getModifier()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Modifier();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Feature#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Type</em>'.
	 * @see bonIDE.Feature#getType()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Type();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Feature#getComment <em>Comment</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Comment</em>'.
	 * @see bonIDE.Feature#getComment()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Comment();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Feature#getArguments <em>Arguments</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Arguments</em>'.
	 * @see bonIDE.Feature#getArguments()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_Arguments();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Feature#getPostConditions <em>Post Conditions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Post Conditions</em>'.
	 * @see bonIDE.Feature#getPostConditions()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_PostConditions();

	/**
	 * Returns the meta object for the containment reference list '{@link bonIDE.Feature#getPreConditions <em>Pre Conditions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Pre Conditions</em>'.
	 * @see bonIDE.Feature#getPreConditions()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_PreConditions();

	/**
	 * Returns the meta object for class '{@link bonIDE.IndexClause <em>Index Clause</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Index Clause</em>'.
	 * @see bonIDE.IndexClause
	 * @generated
	 */
	EClass getIndexClause();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.IndexClause#getIdentifier <em>Identifier</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Identifier</em>'.
	 * @see bonIDE.IndexClause#getIdentifier()
	 * @see #getIndexClause()
	 * @generated
	 */
	EAttribute getIndexClause_Identifier();

	/**
	 * Returns the meta object for the attribute list '{@link bonIDE.IndexClause#getTerms <em>Terms</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Terms</em>'.
	 * @see bonIDE.IndexClause#getTerms()
	 * @see #getIndexClause()
	 * @generated
	 */
	EAttribute getIndexClause_Terms();

	/**
	 * Returns the meta object for class '{@link bonIDE.InheritanceClause <em>Inheritance Clause</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inheritance Clause</em>'.
	 * @see bonIDE.InheritanceClause
	 * @generated
	 */
	EClass getInheritanceClause();

	/**
	 * Returns the meta object for the attribute list '{@link bonIDE.InheritanceClause#getParentNames <em>Parent Names</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Parent Names</em>'.
	 * @see bonIDE.InheritanceClause#getParentNames()
	 * @see #getInheritanceClause()
	 * @generated
	 */
	EAttribute getInheritanceClause_ParentNames();

	/**
	 * Returns the meta object for class '{@link bonIDE.FeatureArgument <em>Feature Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Feature Argument</em>'.
	 * @see bonIDE.FeatureArgument
	 * @generated
	 */
	EClass getFeatureArgument();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.FeatureArgument#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see bonIDE.FeatureArgument#getName()
	 * @see #getFeatureArgument()
	 * @generated
	 */
	EAttribute getFeatureArgument_Name();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.FeatureArgument#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Type</em>'.
	 * @see bonIDE.FeatureArgument#getType()
	 * @see #getFeatureArgument()
	 * @generated
	 */
	EAttribute getFeatureArgument_Type();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.FeatureArgument#getContainerType <em>Container Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Container Type</em>'.
	 * @see bonIDE.FeatureArgument#getContainerType()
	 * @see #getFeatureArgument()
	 * @generated
	 */
	EAttribute getFeatureArgument_ContainerType();

	/**
	 * Returns the meta object for class '{@link bonIDE.PreCondition <em>Pre Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Pre Condition</em>'.
	 * @see bonIDE.PreCondition
	 * @generated
	 */
	EClass getPreCondition();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.PreCondition#getContent <em>Content</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Content</em>'.
	 * @see bonIDE.PreCondition#getContent()
	 * @see #getPreCondition()
	 * @generated
	 */
	EAttribute getPreCondition_Content();

	/**
	 * Returns the meta object for class '{@link bonIDE.PostCondition <em>Post Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Post Condition</em>'.
	 * @see bonIDE.PostCondition
	 * @generated
	 */
	EClass getPostCondition();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.PostCondition#getContent <em>Content</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Content</em>'.
	 * @see bonIDE.PostCondition#getContent()
	 * @see #getPostCondition()
	 * @generated
	 */
	EAttribute getPostCondition_Content();

	/**
	 * Returns the meta object for class '{@link bonIDE.Invariant <em>Invariant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Invariant</em>'.
	 * @see bonIDE.Invariant
	 * @generated
	 */
	EClass getInvariant();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.Invariant#getContent <em>Content</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Content</em>'.
	 * @see bonIDE.Invariant#getContent()
	 * @see #getInvariant()
	 * @generated
	 */
	EAttribute getInvariant_Content();

	/**
	 * Returns the meta object for class '{@link bonIDE.StaticRelationship <em>Static Relationship</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Static Relationship</em>'.
	 * @see bonIDE.StaticRelationship
	 * @generated
	 */
	EClass getStaticRelationship();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.StaticRelationship#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Type</em>'.
	 * @see bonIDE.StaticRelationship#getType()
	 * @see #getStaticRelationship()
	 * @generated
	 */
	EAttribute getStaticRelationship_Type();

	/**
	 * Returns the meta object for the reference '{@link bonIDE.StaticRelationship#getSource <em>Source</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Source</em>'.
	 * @see bonIDE.StaticRelationship#getSource()
	 * @see #getStaticRelationship()
	 * @generated
	 */
	EReference getStaticRelationship_Source();

	/**
	 * Returns the meta object for the reference '{@link bonIDE.StaticRelationship#getTarget <em>Target</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Target</em>'.
	 * @see bonIDE.StaticRelationship#getTarget()
	 * @see #getStaticRelationship()
	 * @generated
	 */
	EReference getStaticRelationship_Target();

	/**
	 * Returns the meta object for class '{@link bonIDE.InheritanceRel <em>Inheritance Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inheritance Rel</em>'.
	 * @see bonIDE.InheritanceRel
	 * @generated
	 */
	EClass getInheritanceRel();

	/**
	 * Returns the meta object for class '{@link bonIDE.ClientSupplierRel <em>Client Supplier Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Client Supplier Rel</em>'.
	 * @see bonIDE.ClientSupplierRel
	 * @generated
	 */
	EClass getClientSupplierRel();

	/**
	 * Returns the meta object for the attribute '{@link bonIDE.ClientSupplierRel#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see bonIDE.ClientSupplierRel#getName()
	 * @see #getClientSupplierRel()
	 * @generated
	 */
	EAttribute getClientSupplierRel_Name();

	/**
	 * Returns the meta object for class '{@link bonIDE.AggregationRel <em>Aggregation Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Aggregation Rel</em>'.
	 * @see bonIDE.AggregationRel
	 * @generated
	 */
	EClass getAggregationRel();

	/**
	 * Returns the meta object for class '{@link bonIDE.AssociationRel <em>Association Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Association Rel</em>'.
	 * @see bonIDE.AssociationRel
	 * @generated
	 */
	EClass getAssociationRel();

	/**
	 * Returns the meta object for enum '{@link bonIDE.ImplementationStatus <em>Implementation Status</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Implementation Status</em>'.
	 * @see bonIDE.ImplementationStatus
	 * @generated
	 */
	EEnum getImplementationStatus();

	/**
	 * Returns the meta object for enum '{@link bonIDE.RelationshipType <em>Relationship Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Relationship Type</em>'.
	 * @see bonIDE.RelationshipType
	 * @generated
	 */
	EEnum getRelationshipType();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	BonIDEFactory getBonIDEFactory();

	/**
	 * <!-- begin-user-doc -->
	 * Defines literals for the meta objects that represent
	 * <ul>
	 *   <li>each class,</li>
	 *   <li>each feature of each class,</li>
	 *   <li>each enum,</li>
	 *   <li>and each data type</li>
	 * </ul>
	 * <!-- end-user-doc -->
	 * @generated
	 */
	interface Literals {
		/**
		 * The meta object literal for the '{@link bonIDE.impl.ModelImpl <em>Model</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.ModelImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getModel()
		 * @generated
		 */
		EClass MODEL = eINSTANCE.getModel();

		/**
		 * The meta object literal for the '<em><b>Abstractions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__ABSTRACTIONS = eINSTANCE.getModel_Abstractions();

		/**
		 * The meta object literal for the '<em><b>Relationships</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__RELATIONSHIPS = eINSTANCE.getModel_Relationships();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.AbstractionImpl <em>Abstraction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.AbstractionImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getAbstraction()
		 * @generated
		 */
		EClass ABSTRACTION = eINSTANCE.getAbstraction();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.ClusterImpl <em>Cluster</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.ClusterImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getCluster()
		 * @generated
		 */
		EClass CLUSTER = eINSTANCE.getCluster();

		/**
		 * The meta object literal for the '<em><b>Contents</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLUSTER__CONTENTS = eINSTANCE.getCluster_Contents();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLUSTER__NAME = eINSTANCE.getCluster_Name();

		/**
		 * The meta object literal for the '<em><b>Collapsed</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLUSTER__COLLAPSED = eINSTANCE.getCluster_Collapsed();

		/**
		 * The meta object literal for the '<em><b>Expanded Height</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLUSTER__EXPANDED_HEIGHT = eINSTANCE.getCluster_ExpandedHeight();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.BONClassImpl <em>BON Class</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.BONClassImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getBONClass()
		 * @generated
		 */
		EClass BON_CLASS = eINSTANCE.getBONClass();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BON_CLASS__NAME = eINSTANCE.getBONClass_Name();

		/**
		 * The meta object literal for the '<em><b>Features</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BON_CLASS__FEATURES = eINSTANCE.getBONClass_Features();

		/**
		 * The meta object literal for the '<em><b>Is Deferred</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BON_CLASS__IS_DEFERRED = eINSTANCE.getBONClass_IsDeferred();

		/**
		 * The meta object literal for the '<em><b>Parents</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BON_CLASS__PARENTS = eINSTANCE.getBONClass_Parents();

		/**
		 * The meta object literal for the '<em><b>Invariants</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BON_CLASS__INVARIANTS = eINSTANCE.getBONClass_Invariants();

		/**
		 * The meta object literal for the '<em><b>Indexes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BON_CLASS__INDEXES = eINSTANCE.getBONClass_Indexes();

		/**
		 * The meta object literal for the '<em><b>Implementation Status</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BON_CLASS__IMPLEMENTATION_STATUS = eINSTANCE.getBONClass_ImplementationStatus();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.StaticAbstractionImpl <em>Static Abstraction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.StaticAbstractionImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getStaticAbstraction()
		 * @generated
		 */
		EClass STATIC_ABSTRACTION = eINSTANCE.getStaticAbstraction();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.FeatureImpl <em>Feature</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.FeatureImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getFeature()
		 * @generated
		 */
		EClass FEATURE = eINSTANCE.getFeature();

		/**
		 * The meta object literal for the '<em><b>Names</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__NAMES = eINSTANCE.getFeature_Names();

		/**
		 * The meta object literal for the '<em><b>Modifier</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__MODIFIER = eINSTANCE.getFeature_Modifier();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__TYPE = eINSTANCE.getFeature_Type();

		/**
		 * The meta object literal for the '<em><b>Comment</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__COMMENT = eINSTANCE.getFeature_Comment();

		/**
		 * The meta object literal for the '<em><b>Arguments</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__ARGUMENTS = eINSTANCE.getFeature_Arguments();

		/**
		 * The meta object literal for the '<em><b>Post Conditions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__POST_CONDITIONS = eINSTANCE.getFeature_PostConditions();

		/**
		 * The meta object literal for the '<em><b>Pre Conditions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__PRE_CONDITIONS = eINSTANCE.getFeature_PreConditions();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.IndexClauseImpl <em>Index Clause</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.IndexClauseImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getIndexClause()
		 * @generated
		 */
		EClass INDEX_CLAUSE = eINSTANCE.getIndexClause();

		/**
		 * The meta object literal for the '<em><b>Identifier</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INDEX_CLAUSE__IDENTIFIER = eINSTANCE.getIndexClause_Identifier();

		/**
		 * The meta object literal for the '<em><b>Terms</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INDEX_CLAUSE__TERMS = eINSTANCE.getIndexClause_Terms();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.InheritanceClauseImpl <em>Inheritance Clause</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.InheritanceClauseImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getInheritanceClause()
		 * @generated
		 */
		EClass INHERITANCE_CLAUSE = eINSTANCE.getInheritanceClause();

		/**
		 * The meta object literal for the '<em><b>Parent Names</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INHERITANCE_CLAUSE__PARENT_NAMES = eINSTANCE.getInheritanceClause_ParentNames();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.FeatureArgumentImpl <em>Feature Argument</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.FeatureArgumentImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getFeatureArgument()
		 * @generated
		 */
		EClass FEATURE_ARGUMENT = eINSTANCE.getFeatureArgument();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE_ARGUMENT__NAME = eINSTANCE.getFeatureArgument_Name();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE_ARGUMENT__TYPE = eINSTANCE.getFeatureArgument_Type();

		/**
		 * The meta object literal for the '<em><b>Container Type</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE_ARGUMENT__CONTAINER_TYPE = eINSTANCE.getFeatureArgument_ContainerType();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.PreConditionImpl <em>Pre Condition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.PreConditionImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getPreCondition()
		 * @generated
		 */
		EClass PRE_CONDITION = eINSTANCE.getPreCondition();

		/**
		 * The meta object literal for the '<em><b>Content</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PRE_CONDITION__CONTENT = eINSTANCE.getPreCondition_Content();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.PostConditionImpl <em>Post Condition</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.PostConditionImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getPostCondition()
		 * @generated
		 */
		EClass POST_CONDITION = eINSTANCE.getPostCondition();

		/**
		 * The meta object literal for the '<em><b>Content</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute POST_CONDITION__CONTENT = eINSTANCE.getPostCondition_Content();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.InvariantImpl <em>Invariant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.InvariantImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getInvariant()
		 * @generated
		 */
		EClass INVARIANT = eINSTANCE.getInvariant();

		/**
		 * The meta object literal for the '<em><b>Content</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INVARIANT__CONTENT = eINSTANCE.getInvariant_Content();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.StaticRelationshipImpl <em>Static Relationship</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.StaticRelationshipImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getStaticRelationship()
		 * @generated
		 */
		EClass STATIC_RELATIONSHIP = eINSTANCE.getStaticRelationship();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STATIC_RELATIONSHIP__TYPE = eINSTANCE.getStaticRelationship_Type();

		/**
		 * The meta object literal for the '<em><b>Source</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATIC_RELATIONSHIP__SOURCE = eINSTANCE.getStaticRelationship_Source();

		/**
		 * The meta object literal for the '<em><b>Target</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference STATIC_RELATIONSHIP__TARGET = eINSTANCE.getStaticRelationship_Target();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.InheritanceRelImpl <em>Inheritance Rel</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.InheritanceRelImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getInheritanceRel()
		 * @generated
		 */
		EClass INHERITANCE_REL = eINSTANCE.getInheritanceRel();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.ClientSupplierRelImpl <em>Client Supplier Rel</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.ClientSupplierRelImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getClientSupplierRel()
		 * @generated
		 */
		EClass CLIENT_SUPPLIER_REL = eINSTANCE.getClientSupplierRel();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLIENT_SUPPLIER_REL__NAME = eINSTANCE.getClientSupplierRel_Name();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.AggregationRelImpl <em>Aggregation Rel</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.AggregationRelImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getAggregationRel()
		 * @generated
		 */
		EClass AGGREGATION_REL = eINSTANCE.getAggregationRel();

		/**
		 * The meta object literal for the '{@link bonIDE.impl.AssociationRelImpl <em>Association Rel</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.impl.AssociationRelImpl
		 * @see bonIDE.impl.BonIDEPackageImpl#getAssociationRel()
		 * @generated
		 */
		EClass ASSOCIATION_REL = eINSTANCE.getAssociationRel();

		/**
		 * The meta object literal for the '{@link bonIDE.ImplementationStatus <em>Implementation Status</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.ImplementationStatus
		 * @see bonIDE.impl.BonIDEPackageImpl#getImplementationStatus()
		 * @generated
		 */
		EEnum IMPLEMENTATION_STATUS = eINSTANCE.getImplementationStatus();

		/**
		 * The meta object literal for the '{@link bonIDE.RelationshipType <em>Relationship Type</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see bonIDE.RelationshipType
		 * @see bonIDE.impl.BonIDEPackageImpl#getRelationshipType()
		 * @generated
		 */
		EEnum RELATIONSHIP_TYPE = eINSTANCE.getRelationshipType();

	}

} //BonIDEPackage

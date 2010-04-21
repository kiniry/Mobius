/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;

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
 * @see BONModel.BONModelFactory
 * @model kind="package"
 * @generated
 */
public interface BONModelPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "BONModel";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "www.ucd.ie/BONModel";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "BONModel";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	BONModelPackage eINSTANCE = BONModel.impl.BONModelPackageImpl.init();

	/**
	 * The meta object id for the '{@link BONModel.impl.ModelImpl <em>Model</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ModelImpl
	 * @see BONModel.impl.BONModelPackageImpl#getModel()
	 * @generated
	 */
	int MODEL = 0;

	/**
	 * The feature id for the '<em><b>Closure</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__CLOSURE = 0;

	/**
	 * The feature id for the '<em><b>Abstractions</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__ABSTRACTIONS = 1;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__RELATIONSHIPS = 2;

	/**
	 * The number of structural features of the '<em>Model</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL_FEATURE_COUNT = 3;

	/**
	 * The meta object id for the '{@link BONModel.impl.RelationshipImpl <em>Relationship</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.RelationshipImpl
	 * @see BONModel.impl.BONModelPackageImpl#getRelationship()
	 * @generated
	 */
	int RELATIONSHIP = 1;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATIONSHIP__SOURCE = 0;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATIONSHIP__TARGET = 1;

	/**
	 * The number of structural features of the '<em>Relationship</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RELATIONSHIP_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link BONModel.impl.AbstractionImpl <em>Abstraction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.AbstractionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getAbstraction()
	 * @generated
	 */
	int ABSTRACTION = 2;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACTION__RELATIONSHIPS = 0;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACTION__CONTAINS = 1;

	/**
	 * The number of structural features of the '<em>Abstraction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ABSTRACTION_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link BONModel.impl.StaticRelationshipImpl <em>Static Relationship</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.StaticRelationshipImpl
	 * @see BONModel.impl.BONModelPackageImpl#getStaticRelationship()
	 * @generated
	 */
	int STATIC_RELATIONSHIP = 3;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP__SOURCE = RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP__TARGET = RELATIONSHIP__TARGET;

	/**
	 * The number of structural features of the '<em>Static Relationship</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_RELATIONSHIP_FEATURE_COUNT = RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.StaticAbstractionImpl <em>Static Abstraction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.StaticAbstractionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getStaticAbstraction()
	 * @generated
	 */
	int STATIC_ABSTRACTION = 4;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_ABSTRACTION__RELATIONSHIPS = ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_ABSTRACTION__CONTAINS = ABSTRACTION__CONTAINS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_ABSTRACTION__NAME = ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Static Abstraction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATIC_ABSTRACTION_FEATURE_COUNT = ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link BONModel.impl.InheritanceImpl <em>Inheritance</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.InheritanceImpl
	 * @see BONModel.impl.BONModelPackageImpl#getInheritance()
	 * @generated
	 */
	int INHERITANCE = 5;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE__SOURCE = STATIC_RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE__TARGET = STATIC_RELATIONSHIP__TARGET;

	/**
	 * The number of structural features of the '<em>Inheritance</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INHERITANCE_FEATURE_COUNT = STATIC_RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.ClientSupplierImpl <em>Client Supplier</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ClientSupplierImpl
	 * @see BONModel.impl.BONModelPackageImpl#getClientSupplier()
	 * @generated
	 */
	int CLIENT_SUPPLIER = 6;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER__SOURCE = STATIC_RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER__TARGET = STATIC_RELATIONSHIP__TARGET;

	/**
	 * The feature id for the '<em><b>Label</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER__LABEL = STATIC_RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Client Supplier</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLIENT_SUPPLIER_FEATURE_COUNT = STATIC_RELATIONSHIP_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link BONModel.impl.AggregationImpl <em>Aggregation</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.AggregationImpl
	 * @see BONModel.impl.BONModelPackageImpl#getAggregation()
	 * @generated
	 */
	int AGGREGATION = 7;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION__SOURCE = CLIENT_SUPPLIER__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION__TARGET = CLIENT_SUPPLIER__TARGET;

	/**
	 * The feature id for the '<em><b>Label</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION__LABEL = CLIENT_SUPPLIER__LABEL;

	/**
	 * The number of structural features of the '<em>Aggregation</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AGGREGATION_FEATURE_COUNT = CLIENT_SUPPLIER_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.AssociationImpl <em>Association</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.AssociationImpl
	 * @see BONModel.impl.BONModelPackageImpl#getAssociation()
	 * @generated
	 */
	int ASSOCIATION = 8;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION__SOURCE = CLIENT_SUPPLIER__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION__TARGET = CLIENT_SUPPLIER__TARGET;

	/**
	 * The feature id for the '<em><b>Label</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION__LABEL = CLIENT_SUPPLIER__LABEL;

	/**
	 * The number of structural features of the '<em>Association</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSOCIATION_FEATURE_COUNT = CLIENT_SUPPLIER_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.MessageImpl <em>Message</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.MessageImpl
	 * @see BONModel.impl.BONModelPackageImpl#getMessage()
	 * @generated
	 */
	int MESSAGE = 9;

	/**
	 * The feature id for the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MESSAGE__SOURCE = RELATIONSHIP__SOURCE;

	/**
	 * The feature id for the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MESSAGE__TARGET = RELATIONSHIP__TARGET;

	/**
	 * The number of structural features of the '<em>Message</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MESSAGE_FEATURE_COUNT = RELATIONSHIP_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.ClusterImpl <em>Cluster</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ClusterImpl
	 * @see BONModel.impl.BONModelPackageImpl#getCluster()
	 * @generated
	 */
	int CLUSTER = 10;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__RELATIONSHIPS = STATIC_ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__CONTAINS = STATIC_ABSTRACTION__CONTAINS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__NAME = STATIC_ABSTRACTION__NAME;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER__CONTENTS = STATIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Cluster</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLUSTER_FEATURE_COUNT = STATIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link BONModel.impl.ClassImpl <em>Class</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ClassImpl
	 * @see BONModel.impl.BONModelPackageImpl#getClass_()
	 * @generated
	 */
	int CLASS = 11;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__RELATIONSHIPS = STATIC_ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__CONTAINS = STATIC_ABSTRACTION__CONTAINS;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__NAME = STATIC_ABSTRACTION__NAME;

	/**
	 * The feature id for the '<em><b>Calls In Invariants</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__CALLS_IN_INVARIANTS = STATIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Client Features</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__CLIENT_FEATURES = STATIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Renamings</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__RENAMINGS = STATIC_ABSTRACTION_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Rename Class Parents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__RENAME_CLASS_PARENTS = STATIC_ABSTRACTION_FEATURE_COUNT + 3;

	/**
	 * The feature id for the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IS_DEFERRED = STATIC_ABSTRACTION_FEATURE_COUNT + 4;

	/**
	 * The feature id for the '<em><b>Is Effective</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IS_EFFECTIVE = STATIC_ABSTRACTION_FEATURE_COUNT + 5;

	/**
	 * The feature id for the '<em><b>Is Persistent</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IS_PERSISTENT = STATIC_ABSTRACTION_FEATURE_COUNT + 6;

	/**
	 * The feature id for the '<em><b>Is External</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IS_EXTERNAL = STATIC_ABSTRACTION_FEATURE_COUNT + 7;

	/**
	 * The feature id for the '<em><b>Is Root</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IS_ROOT = STATIC_ABSTRACTION_FEATURE_COUNT + 8;

	/**
	 * The feature id for the '<em><b>Redefined</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__REDEFINED = STATIC_ABSTRACTION_FEATURE_COUNT + 9;

	/**
	 * The feature id for the '<em><b>All Names</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__ALL_NAMES = STATIC_ABSTRACTION_FEATURE_COUNT + 10;

	/**
	 * The feature id for the '<em><b>Invariant</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__INVARIANT = STATIC_ABSTRACTION_FEATURE_COUNT + 11;

	/**
	 * The feature id for the '<em><b>Features</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__FEATURES = STATIC_ABSTRACTION_FEATURE_COUNT + 12;

	/**
	 * The number of structural features of the '<em>Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_FEATURE_COUNT = STATIC_ABSTRACTION_FEATURE_COUNT + 13;

	/**
	 * The meta object id for the '{@link BONModel.impl.CallImpl <em>Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.CallImpl
	 * @see BONModel.impl.BONModelPackageImpl#getCall()
	 * @generated
	 */
	int CALL = 12;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL__ARGUMENTS = 0;

	/**
	 * The feature id for the '<em><b>Feature</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL__FEATURE = 1;

	/**
	 * The feature id for the '<em><b>Entity</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL__ENTITY = 2;

	/**
	 * The number of structural features of the '<em>Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CALL_FEATURE_COUNT = 3;

	/**
	 * The meta object id for the '{@link BONModel.impl.FeatureImpl <em>Feature</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.FeatureImpl
	 * @see BONModel.impl.BONModelPackageImpl#getFeature()
	 * @generated
	 */
	int FEATURE = 13;

	/**
	 * The feature id for the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__IS_DEFERRED = 0;

	/**
	 * The feature id for the '<em><b>Is Effective</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__IS_EFFECTIVE = 1;

	/**
	 * The feature id for the '<em><b>Is Redefined</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__IS_REDEFINED = 2;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__NAME = 3;

	/**
	 * The feature id for the '<em><b>Comment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__COMMENT = 4;

	/**
	 * The feature id for the '<em><b>Accessors</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__ACCESSORS = 5;

	/**
	 * The feature id for the '<em><b>Calls In Precondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__CALLS_IN_PRECONDITION = 6;

	/**
	 * The feature id for the '<em><b>Calls In Postcondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__CALLS_IN_POSTCONDITION = 7;

	/**
	 * The feature id for the '<em><b>Frame</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__FRAME = 8;

	/**
	 * The feature id for the '<em><b>Post Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__POST_CONDITION = 9;

	/**
	 * The feature id for the '<em><b>Pre Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__PRE_CONDITION = 10;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__PARAMETERS = 11;

	/**
	 * The feature id for the '<em><b>Pre Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__PRE_CONDITION_STRING = 12;

	/**
	 * The feature id for the '<em><b>Post Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__POST_CONDITION_STRING = 13;

	/**
	 * The number of structural features of the '<em>Feature</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_FEATURE_COUNT = 14;

	/**
	 * The meta object id for the '{@link BONModel.impl.RenamingImpl <em>Renaming</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.RenamingImpl
	 * @see BONModel.impl.BONModelPackageImpl#getRenaming()
	 * @generated
	 */
	int RENAMING = 14;

	/**
	 * The number of structural features of the '<em>Renaming</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RENAMING_FEATURE_COUNT = 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.DynamicAbstractionImpl <em>Dynamic Abstraction</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.DynamicAbstractionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getDynamicAbstraction()
	 * @generated
	 */
	int DYNAMIC_ABSTRACTION = 15;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DYNAMIC_ABSTRACTION__RELATIONSHIPS = ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DYNAMIC_ABSTRACTION__CONTAINS = ABSTRACTION__CONTAINS;

	/**
	 * The number of structural features of the '<em>Dynamic Abstraction</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DYNAMIC_ABSTRACTION_FEATURE_COUNT = ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.ObjectImpl <em>Object</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ObjectImpl
	 * @see BONModel.impl.BONModelPackageImpl#getObject()
	 * @generated
	 */
	int OBJECT = 16;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT__RELATIONSHIPS = DYNAMIC_ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT__CONTAINS = DYNAMIC_ABSTRACTION__CONTAINS;

	/**
	 * The feature id for the '<em><b>Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT__CLASS = DYNAMIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Object</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_FEATURE_COUNT = DYNAMIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link BONModel.impl.ObjectClusterImpl <em>Object Cluster</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ObjectClusterImpl
	 * @see BONModel.impl.BONModelPackageImpl#getObjectCluster()
	 * @generated
	 */
	int OBJECT_CLUSTER = 17;

	/**
	 * The feature id for the '<em><b>Relationships</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_CLUSTER__RELATIONSHIPS = DYNAMIC_ABSTRACTION__RELATIONSHIPS;

	/**
	 * The feature id for the '<em><b>Contains</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_CLUSTER__CONTAINS = DYNAMIC_ABSTRACTION__CONTAINS;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_CLUSTER__CONTENTS = DYNAMIC_ABSTRACTION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Object Cluster</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OBJECT_CLUSTER_FEATURE_COUNT = DYNAMIC_ABSTRACTION_FEATURE_COUNT + 1;

	/**
	 * The meta object id for the '{@link BONModel.impl.CommandImpl <em>Command</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.CommandImpl
	 * @see BONModel.impl.BONModelPackageImpl#getCommand()
	 * @generated
	 */
	int COMMAND = 18;

	/**
	 * The feature id for the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__IS_DEFERRED = FEATURE__IS_DEFERRED;

	/**
	 * The feature id for the '<em><b>Is Effective</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__IS_EFFECTIVE = FEATURE__IS_EFFECTIVE;

	/**
	 * The feature id for the '<em><b>Is Redefined</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__IS_REDEFINED = FEATURE__IS_REDEFINED;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__NAME = FEATURE__NAME;

	/**
	 * The feature id for the '<em><b>Comment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__COMMENT = FEATURE__COMMENT;

	/**
	 * The feature id for the '<em><b>Accessors</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__ACCESSORS = FEATURE__ACCESSORS;

	/**
	 * The feature id for the '<em><b>Calls In Precondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__CALLS_IN_PRECONDITION = FEATURE__CALLS_IN_PRECONDITION;

	/**
	 * The feature id for the '<em><b>Calls In Postcondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__CALLS_IN_POSTCONDITION = FEATURE__CALLS_IN_POSTCONDITION;

	/**
	 * The feature id for the '<em><b>Frame</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__FRAME = FEATURE__FRAME;

	/**
	 * The feature id for the '<em><b>Post Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__POST_CONDITION = FEATURE__POST_CONDITION;

	/**
	 * The feature id for the '<em><b>Pre Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__PRE_CONDITION = FEATURE__PRE_CONDITION;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__PARAMETERS = FEATURE__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Pre Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__PRE_CONDITION_STRING = FEATURE__PRE_CONDITION_STRING;

	/**
	 * The feature id for the '<em><b>Post Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND__POST_CONDITION_STRING = FEATURE__POST_CONDITION_STRING;

	/**
	 * The number of structural features of the '<em>Command</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int COMMAND_FEATURE_COUNT = FEATURE_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.QueryImpl <em>Query</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.QueryImpl
	 * @see BONModel.impl.BONModelPackageImpl#getQuery()
	 * @generated
	 */
	int QUERY = 19;

	/**
	 * The feature id for the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__IS_DEFERRED = FEATURE__IS_DEFERRED;

	/**
	 * The feature id for the '<em><b>Is Effective</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__IS_EFFECTIVE = FEATURE__IS_EFFECTIVE;

	/**
	 * The feature id for the '<em><b>Is Redefined</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__IS_REDEFINED = FEATURE__IS_REDEFINED;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__NAME = FEATURE__NAME;

	/**
	 * The feature id for the '<em><b>Comment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__COMMENT = FEATURE__COMMENT;

	/**
	 * The feature id for the '<em><b>Accessors</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__ACCESSORS = FEATURE__ACCESSORS;

	/**
	 * The feature id for the '<em><b>Calls In Precondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__CALLS_IN_PRECONDITION = FEATURE__CALLS_IN_PRECONDITION;

	/**
	 * The feature id for the '<em><b>Calls In Postcondition</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__CALLS_IN_POSTCONDITION = FEATURE__CALLS_IN_POSTCONDITION;

	/**
	 * The feature id for the '<em><b>Frame</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__FRAME = FEATURE__FRAME;

	/**
	 * The feature id for the '<em><b>Post Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__POST_CONDITION = FEATURE__POST_CONDITION;

	/**
	 * The feature id for the '<em><b>Pre Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__PRE_CONDITION = FEATURE__PRE_CONDITION;

	/**
	 * The feature id for the '<em><b>Parameters</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__PARAMETERS = FEATURE__PARAMETERS;

	/**
	 * The feature id for the '<em><b>Pre Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__PRE_CONDITION_STRING = FEATURE__PRE_CONDITION_STRING;

	/**
	 * The feature id for the '<em><b>Post Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__POST_CONDITION_STRING = FEATURE__POST_CONDITION_STRING;

	/**
	 * The feature id for the '<em><b>Result</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__RESULT = FEATURE_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>No Contract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY__NO_CONTRACT = FEATURE_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Query</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int QUERY_FEATURE_COUNT = FEATURE_FEATURE_COUNT + 2;

	/**
	 * The meta object id for the '{@link BONModel.impl.ParameterImpl <em>Parameter</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ParameterImpl
	 * @see BONModel.impl.BONModelPackageImpl#getParameter()
	 * @generated
	 */
	int PARAMETER = 20;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__NAME = 0;

	/**
	 * The feature id for the '<em><b>Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__TYPE = 1;

	/**
	 * The number of structural features of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link BONModel.impl.DirectCallImpl <em>Direct Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.DirectCallImpl
	 * @see BONModel.impl.BONModelPackageImpl#getDirectCall()
	 * @generated
	 */
	int DIRECT_CALL = 21;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIRECT_CALL__ARGUMENTS = CALL__ARGUMENTS;

	/**
	 * The feature id for the '<em><b>Feature</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIRECT_CALL__FEATURE = CALL__FEATURE;

	/**
	 * The feature id for the '<em><b>Entity</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIRECT_CALL__ENTITY = CALL__ENTITY;

	/**
	 * The number of structural features of the '<em>Direct Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIRECT_CALL_FEATURE_COUNT = CALL_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.ChainedCallImpl <em>Chained Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ChainedCallImpl
	 * @see BONModel.impl.BONModelPackageImpl#getChainedCall()
	 * @generated
	 */
	int CHAINED_CALL = 22;

	/**
	 * The feature id for the '<em><b>Arguments</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHAINED_CALL__ARGUMENTS = CALL__ARGUMENTS;

	/**
	 * The feature id for the '<em><b>Feature</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHAINED_CALL__FEATURE = CALL__FEATURE;

	/**
	 * The feature id for the '<em><b>Entity</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHAINED_CALL__ENTITY = CALL__ENTITY;

	/**
	 * The feature id for the '<em><b>Chain</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHAINED_CALL__CHAIN = CALL_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Chained Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CHAINED_CALL_FEATURE_COUNT = CALL_FEATURE_COUNT + 1;


	/**
	 * The meta object id for the '{@link BONModel.impl.ExpressionImpl <em>Expression</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.ExpressionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getExpression()
	 * @generated
	 */
	int EXPRESSION = 23;

	/**
	 * The feature id for the '<em><b>Result Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION__RESULT_TYPE = 0;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION__CONTENTS = 1;

	/**
	 * The number of structural features of the '<em>Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link BONModel.impl.BooleanExpressionImpl <em>Boolean Expression</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.BooleanExpressionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getBooleanExpression()
	 * @generated
	 */
	int BOOLEAN_EXPRESSION = 24;

	/**
	 * The feature id for the '<em><b>Result Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_EXPRESSION__RESULT_TYPE = EXPRESSION__RESULT_TYPE;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_EXPRESSION__CONTENTS = EXPRESSION__CONTENTS;

	/**
	 * The number of structural features of the '<em>Boolean Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_EXPRESSION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.AssertionImpl <em>Assertion</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.AssertionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getAssertion()
	 * @generated
	 */
	int ASSERTION = 25;

	/**
	 * The feature id for the '<em><b>Result Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__RESULT_TYPE = BOOLEAN_EXPRESSION__RESULT_TYPE;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION__CONTENTS = BOOLEAN_EXPRESSION__CONTENTS;

	/**
	 * The number of structural features of the '<em>Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSERTION_FEATURE_COUNT = BOOLEAN_EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.SingleStateAssertionImpl <em>Single State Assertion</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.SingleStateAssertionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getSingleStateAssertion()
	 * @generated
	 */
	int SINGLE_STATE_ASSERTION = 26;

	/**
	 * The feature id for the '<em><b>Result Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_STATE_ASSERTION__RESULT_TYPE = ASSERTION__RESULT_TYPE;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_STATE_ASSERTION__CONTENTS = ASSERTION__CONTENTS;

	/**
	 * The number of structural features of the '<em>Single State Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_STATE_ASSERTION_FEATURE_COUNT = ASSERTION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.DoubleStateAssertionImpl <em>Double State Assertion</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.DoubleStateAssertionImpl
	 * @see BONModel.impl.BONModelPackageImpl#getDoubleStateAssertion()
	 * @generated
	 */
	int DOUBLE_STATE_ASSERTION = 27;

	/**
	 * The feature id for the '<em><b>Result Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DOUBLE_STATE_ASSERTION__RESULT_TYPE = ASSERTION__RESULT_TYPE;

	/**
	 * The feature id for the '<em><b>Contents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DOUBLE_STATE_ASSERTION__CONTENTS = ASSERTION__CONTENTS;

	/**
	 * The number of structural features of the '<em>Double State Assertion</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DOUBLE_STATE_ASSERTION_FEATURE_COUNT = ASSERTION_FEATURE_COUNT + 0;

	/**
	 * The meta object id for the '{@link BONModel.impl.EntityImpl <em>Entity</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.impl.EntityImpl
	 * @see BONModel.impl.BONModelPackageImpl#getEntity()
	 * @generated
	 */
	int ENTITY = 28;

	/**
	 * The number of structural features of the '<em>Entity</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ENTITY_FEATURE_COUNT = 0;


	/**
	 * The meta object id for the '{@link BONModel.RelationshipType <em>Relationship Type</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see BONModel.RelationshipType
	 * @see BONModel.impl.BONModelPackageImpl#getRelationshipType()
	 * @generated
	 */
	int RELATIONSHIP_TYPE = 29;


	/**
	 * Returns the meta object for class '{@link BONModel.Model <em>Model</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Model</em>'.
	 * @see BONModel.Model
	 * @generated
	 */
	EClass getModel();

	/**
	 * Returns the meta object for the containment reference list '{@link BONModel.Model#getRelationships <em>Relationships</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Relationships</em>'.
	 * @see BONModel.Model#getRelationships()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Relationships();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Model#getClosure <em>Closure</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Closure</em>'.
	 * @see BONModel.Model#getClosure()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Closure();

	/**
	 * Returns the meta object for the containment reference list '{@link BONModel.Model#getAbstractions <em>Abstractions</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Abstractions</em>'.
	 * @see BONModel.Model#getAbstractions()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Abstractions();

	/**
	 * Returns the meta object for class '{@link BONModel.Relationship <em>Relationship</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Relationship</em>'.
	 * @see BONModel.Relationship
	 * @generated
	 */
	EClass getRelationship();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Relationship#getSource <em>Source</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Source</em>'.
	 * @see BONModel.Relationship#getSource()
	 * @see #getRelationship()
	 * @generated
	 */
	EReference getRelationship_Source();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Relationship#getTarget <em>Target</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Target</em>'.
	 * @see BONModel.Relationship#getTarget()
	 * @see #getRelationship()
	 * @generated
	 */
	EReference getRelationship_Target();

	/**
	 * Returns the meta object for class '{@link BONModel.Abstraction <em>Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Abstraction</em>'.
	 * @see BONModel.Abstraction
	 * @generated
	 */
	EClass getAbstraction();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Abstraction#getRelationships <em>Relationships</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Relationships</em>'.
	 * @see BONModel.Abstraction#getRelationships()
	 * @see #getAbstraction()
	 * @generated
	 */
	EReference getAbstraction_Relationships();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Abstraction#getContains <em>Contains</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Contains</em>'.
	 * @see BONModel.Abstraction#getContains()
	 * @see #getAbstraction()
	 * @generated
	 */
	EReference getAbstraction_Contains();

	/**
	 * Returns the meta object for class '{@link BONModel.StaticRelationship <em>Static Relationship</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Static Relationship</em>'.
	 * @see BONModel.StaticRelationship
	 * @generated
	 */
	EClass getStaticRelationship();

	/**
	 * Returns the meta object for class '{@link BONModel.StaticAbstraction <em>Static Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Static Abstraction</em>'.
	 * @see BONModel.StaticAbstraction
	 * @generated
	 */
	EClass getStaticAbstraction();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.StaticAbstraction#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see BONModel.StaticAbstraction#getName()
	 * @see #getStaticAbstraction()
	 * @generated
	 */
	EAttribute getStaticAbstraction_Name();

	/**
	 * Returns the meta object for class '{@link BONModel.Inheritance <em>Inheritance</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inheritance</em>'.
	 * @see BONModel.Inheritance
	 * @generated
	 */
	EClass getInheritance();

	/**
	 * Returns the meta object for class '{@link BONModel.ClientSupplier <em>Client Supplier</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Client Supplier</em>'.
	 * @see BONModel.ClientSupplier
	 * @generated
	 */
	EClass getClientSupplier();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.ClientSupplier#getLabel <em>Label</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Label</em>'.
	 * @see BONModel.ClientSupplier#getLabel()
	 * @see #getClientSupplier()
	 * @generated
	 */
	EAttribute getClientSupplier_Label();

	/**
	 * Returns the meta object for class '{@link BONModel.Aggregation <em>Aggregation</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Aggregation</em>'.
	 * @see BONModel.Aggregation
	 * @generated
	 */
	EClass getAggregation();

	/**
	 * Returns the meta object for class '{@link BONModel.Association <em>Association</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Association</em>'.
	 * @see BONModel.Association
	 * @generated
	 */
	EClass getAssociation();

	/**
	 * Returns the meta object for class '{@link BONModel.Message <em>Message</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Message</em>'.
	 * @see BONModel.Message
	 * @generated
	 */
	EClass getMessage();

	/**
	 * Returns the meta object for class '{@link BONModel.Cluster <em>Cluster</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Cluster</em>'.
	 * @see BONModel.Cluster
	 * @generated
	 */
	EClass getCluster();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Cluster#getContents <em>Contents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Contents</em>'.
	 * @see BONModel.Cluster#getContents()
	 * @see #getCluster()
	 * @generated
	 */
	EReference getCluster_Contents();

	/**
	 * Returns the meta object for class '{@link BONModel.Class <em>Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class</em>'.
	 * @see BONModel.Class
	 * @generated
	 */
	EClass getClass_();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Class#getCallsInInvariants <em>Calls In Invariants</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Calls In Invariants</em>'.
	 * @see BONModel.Class#getCallsInInvariants()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_CallsInInvariants();

	/**
	 * Returns the meta object for the containment reference list '{@link BONModel.Class#getFeatures <em>Features</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Features</em>'.
	 * @see BONModel.Class#getFeatures()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_Features();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Class#getClientFeatures <em>Client Features</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Client Features</em>'.
	 * @see BONModel.Class#getClientFeatures()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_ClientFeatures();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Class#getRenamings <em>Renamings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Renamings</em>'.
	 * @see BONModel.Class#getRenamings()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_Renamings();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Class#getRenameClassParents <em>Rename Class Parents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Rename Class Parents</em>'.
	 * @see BONModel.Class#getRenameClassParents()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_RenameClassParents();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Class#isIsDeferred <em>Is Deferred</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Deferred</em>'.
	 * @see BONModel.Class#isIsDeferred()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_IsDeferred();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Class#isIsEffective <em>Is Effective</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Effective</em>'.
	 * @see BONModel.Class#isIsEffective()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_IsEffective();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Class#isIsPersistent <em>Is Persistent</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Persistent</em>'.
	 * @see BONModel.Class#isIsPersistent()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_IsPersistent();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Class#isIsExternal <em>Is External</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is External</em>'.
	 * @see BONModel.Class#isIsExternal()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_IsExternal();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Class#isIsRoot <em>Is Root</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Root</em>'.
	 * @see BONModel.Class#isIsRoot()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_IsRoot();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Class#getRedefined <em>Redefined</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Redefined</em>'.
	 * @see BONModel.Class#getRedefined()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_Redefined();

	/**
	 * Returns the meta object for the attribute list '{@link BONModel.Class#getAllNames <em>All Names</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>All Names</em>'.
	 * @see BONModel.Class#getAllNames()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_AllNames();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Class#getInvariant <em>Invariant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Invariant</em>'.
	 * @see BONModel.Class#getInvariant()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_Invariant();

	/**
	 * Returns the meta object for class '{@link BONModel.Call <em>Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Call</em>'.
	 * @see BONModel.Call
	 * @generated
	 */
	EClass getCall();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Call#getArguments <em>Arguments</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Arguments</em>'.
	 * @see BONModel.Call#getArguments()
	 * @see #getCall()
	 * @generated
	 */
	EReference getCall_Arguments();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Call#getFeature <em>Feature</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Feature</em>'.
	 * @see BONModel.Call#getFeature()
	 * @see #getCall()
	 * @generated
	 */
	EReference getCall_Feature();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Call#getEntity <em>Entity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Entity</em>'.
	 * @see BONModel.Call#getEntity()
	 * @see #getCall()
	 * @generated
	 */
	EReference getCall_Entity();

	/**
	 * Returns the meta object for class '{@link BONModel.Feature <em>Feature</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Feature</em>'.
	 * @see BONModel.Feature
	 * @generated
	 */
	EClass getFeature();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#isIsDeferred <em>Is Deferred</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Deferred</em>'.
	 * @see BONModel.Feature#isIsDeferred()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_IsDeferred();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#isIsEffective <em>Is Effective</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Effective</em>'.
	 * @see BONModel.Feature#isIsEffective()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_IsEffective();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#isIsRedefined <em>Is Redefined</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Is Redefined</em>'.
	 * @see BONModel.Feature#isIsRedefined()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_IsRedefined();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see BONModel.Feature#getName()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Name();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#getComment <em>Comment</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Comment</em>'.
	 * @see BONModel.Feature#getComment()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Comment();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Feature#getAccessors <em>Accessors</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Accessors</em>'.
	 * @see BONModel.Feature#getAccessors()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_Accessors();

	/**
	 * Returns the meta object for the containment reference list '{@link BONModel.Feature#getParameters <em>Parameters</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Parameters</em>'.
	 * @see BONModel.Feature#getParameters()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_Parameters();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#getPreConditionString <em>Pre Condition String</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Pre Condition String</em>'.
	 * @see BONModel.Feature#getPreConditionString()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_PreConditionString();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Feature#getPostConditionString <em>Post Condition String</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Post Condition String</em>'.
	 * @see BONModel.Feature#getPostConditionString()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_PostConditionString();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Feature#getCallsInPrecondition <em>Calls In Precondition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Calls In Precondition</em>'.
	 * @see BONModel.Feature#getCallsInPrecondition()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_CallsInPrecondition();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Feature#getCallsInPostcondition <em>Calls In Postcondition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Calls In Postcondition</em>'.
	 * @see BONModel.Feature#getCallsInPostcondition()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_CallsInPostcondition();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.Feature#getFrame <em>Frame</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Frame</em>'.
	 * @see BONModel.Feature#getFrame()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_Frame();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Feature#getPostCondition <em>Post Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Post Condition</em>'.
	 * @see BONModel.Feature#getPostCondition()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_PostCondition();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Feature#getPreCondition <em>Pre Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Pre Condition</em>'.
	 * @see BONModel.Feature#getPreCondition()
	 * @see #getFeature()
	 * @generated
	 */
	EReference getFeature_PreCondition();

	/**
	 * Returns the meta object for class '{@link BONModel.Renaming <em>Renaming</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Renaming</em>'.
	 * @see BONModel.Renaming
	 * @generated
	 */
	EClass getRenaming();

	/**
	 * Returns the meta object for class '{@link BONModel.DynamicAbstraction <em>Dynamic Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Dynamic Abstraction</em>'.
	 * @see BONModel.DynamicAbstraction
	 * @generated
	 */
	EClass getDynamicAbstraction();

	/**
	 * Returns the meta object for class '{@link BONModel.Object <em>Object</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object</em>'.
	 * @see BONModel.Object
	 * @generated
	 */
	EClass getObject();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Object#getClass_ <em>Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Class</em>'.
	 * @see BONModel.Object#getClass_()
	 * @see #getObject()
	 * @generated
	 */
	EReference getObject_Class();

	/**
	 * Returns the meta object for class '{@link BONModel.ObjectCluster <em>Object Cluster</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Object Cluster</em>'.
	 * @see BONModel.ObjectCluster
	 * @generated
	 */
	EClass getObjectCluster();

	/**
	 * Returns the meta object for the reference list '{@link BONModel.ObjectCluster#getContents <em>Contents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Contents</em>'.
	 * @see BONModel.ObjectCluster#getContents()
	 * @see #getObjectCluster()
	 * @generated
	 */
	EReference getObjectCluster_Contents();

	/**
	 * Returns the meta object for class '{@link BONModel.Command <em>Command</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Command</em>'.
	 * @see BONModel.Command
	 * @generated
	 */
	EClass getCommand();

	/**
	 * Returns the meta object for class '{@link BONModel.Query <em>Query</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Query</em>'.
	 * @see BONModel.Query
	 * @generated
	 */
	EClass getQuery();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Query#getResult <em>Result</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Result</em>'.
	 * @see BONModel.Query#getResult()
	 * @see #getQuery()
	 * @generated
	 */
	EReference getQuery_Result();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Query#isNoContract <em>No Contract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>No Contract</em>'.
	 * @see BONModel.Query#isNoContract()
	 * @see #getQuery()
	 * @generated
	 */
	EAttribute getQuery_NoContract();

	/**
	 * Returns the meta object for class '{@link BONModel.Parameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Parameter</em>'.
	 * @see BONModel.Parameter
	 * @generated
	 */
	EClass getParameter();

	/**
	 * Returns the meta object for the attribute '{@link BONModel.Parameter#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see BONModel.Parameter#getName()
	 * @see #getParameter()
	 * @generated
	 */
	EAttribute getParameter_Name();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Parameter#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Type</em>'.
	 * @see BONModel.Parameter#getType()
	 * @see #getParameter()
	 * @generated
	 */
	EReference getParameter_Type();

	/**
	 * Returns the meta object for class '{@link BONModel.DirectCall <em>Direct Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Direct Call</em>'.
	 * @see BONModel.DirectCall
	 * @generated
	 */
	EClass getDirectCall();

	/**
	 * Returns the meta object for class '{@link BONModel.ChainedCall <em>Chained Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Chained Call</em>'.
	 * @see BONModel.ChainedCall
	 * @generated
	 */
	EClass getChainedCall();

	/**
	 * Returns the meta object for the reference '{@link BONModel.ChainedCall#getChain <em>Chain</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Chain</em>'.
	 * @see BONModel.ChainedCall#getChain()
	 * @see #getChainedCall()
	 * @generated
	 */
	EReference getChainedCall_Chain();

	/**
	 * Returns the meta object for class '{@link BONModel.Expression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expression</em>'.
	 * @see BONModel.Expression
	 * @generated
	 */
	EClass getExpression();

	/**
	 * Returns the meta object for the reference '{@link BONModel.Expression#getResultType <em>Result Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Result Type</em>'.
	 * @see BONModel.Expression#getResultType()
	 * @see #getExpression()
	 * @generated
	 */
	EReference getExpression_ResultType();

	/**
	 * Returns the meta object for the attribute list '{@link BONModel.Expression#getContents <em>Contents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Contents</em>'.
	 * @see BONModel.Expression#getContents()
	 * @see #getExpression()
	 * @generated
	 */
	EAttribute getExpression_Contents();

	/**
	 * Returns the meta object for class '{@link BONModel.BooleanExpression <em>Boolean Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Boolean Expression</em>'.
	 * @see BONModel.BooleanExpression
	 * @generated
	 */
	EClass getBooleanExpression();

	/**
	 * Returns the meta object for class '{@link BONModel.Assertion <em>Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assertion</em>'.
	 * @see BONModel.Assertion
	 * @generated
	 */
	EClass getAssertion();

	/**
	 * Returns the meta object for class '{@link BONModel.SingleStateAssertion <em>Single State Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Single State Assertion</em>'.
	 * @see BONModel.SingleStateAssertion
	 * @generated
	 */
	EClass getSingleStateAssertion();

	/**
	 * Returns the meta object for class '{@link BONModel.DoubleStateAssertion <em>Double State Assertion</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Double State Assertion</em>'.
	 * @see BONModel.DoubleStateAssertion
	 * @generated
	 */
	EClass getDoubleStateAssertion();

	/**
	 * Returns the meta object for class '{@link BONModel.Entity <em>Entity</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Entity</em>'.
	 * @see BONModel.Entity
	 * @generated
	 */
	EClass getEntity();

	/**
	 * Returns the meta object for enum '{@link BONModel.RelationshipType <em>Relationship Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Relationship Type</em>'.
	 * @see BONModel.RelationshipType
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
	BONModelFactory getBONModelFactory();

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
		 * The meta object literal for the '{@link BONModel.impl.ModelImpl <em>Model</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ModelImpl
		 * @see BONModel.impl.BONModelPackageImpl#getModel()
		 * @generated
		 */
		EClass MODEL = eINSTANCE.getModel();

		/**
		 * The meta object literal for the '<em><b>Relationships</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__RELATIONSHIPS = eINSTANCE.getModel_Relationships();

		/**
		 * The meta object literal for the '<em><b>Closure</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__CLOSURE = eINSTANCE.getModel_Closure();

		/**
		 * The meta object literal for the '<em><b>Abstractions</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__ABSTRACTIONS = eINSTANCE.getModel_Abstractions();

		/**
		 * The meta object literal for the '{@link BONModel.impl.RelationshipImpl <em>Relationship</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.RelationshipImpl
		 * @see BONModel.impl.BONModelPackageImpl#getRelationship()
		 * @generated
		 */
		EClass RELATIONSHIP = eINSTANCE.getRelationship();

		/**
		 * The meta object literal for the '<em><b>Source</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RELATIONSHIP__SOURCE = eINSTANCE.getRelationship_Source();

		/**
		 * The meta object literal for the '<em><b>Target</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RELATIONSHIP__TARGET = eINSTANCE.getRelationship_Target();

		/**
		 * The meta object literal for the '{@link BONModel.impl.AbstractionImpl <em>Abstraction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.AbstractionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getAbstraction()
		 * @generated
		 */
		EClass ABSTRACTION = eINSTANCE.getAbstraction();

		/**
		 * The meta object literal for the '<em><b>Relationships</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ABSTRACTION__RELATIONSHIPS = eINSTANCE.getAbstraction_Relationships();

		/**
		 * The meta object literal for the '<em><b>Contains</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ABSTRACTION__CONTAINS = eINSTANCE.getAbstraction_Contains();

		/**
		 * The meta object literal for the '{@link BONModel.impl.StaticRelationshipImpl <em>Static Relationship</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.StaticRelationshipImpl
		 * @see BONModel.impl.BONModelPackageImpl#getStaticRelationship()
		 * @generated
		 */
		EClass STATIC_RELATIONSHIP = eINSTANCE.getStaticRelationship();

		/**
		 * The meta object literal for the '{@link BONModel.impl.StaticAbstractionImpl <em>Static Abstraction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.StaticAbstractionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getStaticAbstraction()
		 * @generated
		 */
		EClass STATIC_ABSTRACTION = eINSTANCE.getStaticAbstraction();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STATIC_ABSTRACTION__NAME = eINSTANCE.getStaticAbstraction_Name();

		/**
		 * The meta object literal for the '{@link BONModel.impl.InheritanceImpl <em>Inheritance</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.InheritanceImpl
		 * @see BONModel.impl.BONModelPackageImpl#getInheritance()
		 * @generated
		 */
		EClass INHERITANCE = eINSTANCE.getInheritance();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ClientSupplierImpl <em>Client Supplier</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ClientSupplierImpl
		 * @see BONModel.impl.BONModelPackageImpl#getClientSupplier()
		 * @generated
		 */
		EClass CLIENT_SUPPLIER = eINSTANCE.getClientSupplier();

		/**
		 * The meta object literal for the '<em><b>Label</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLIENT_SUPPLIER__LABEL = eINSTANCE.getClientSupplier_Label();

		/**
		 * The meta object literal for the '{@link BONModel.impl.AggregationImpl <em>Aggregation</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.AggregationImpl
		 * @see BONModel.impl.BONModelPackageImpl#getAggregation()
		 * @generated
		 */
		EClass AGGREGATION = eINSTANCE.getAggregation();

		/**
		 * The meta object literal for the '{@link BONModel.impl.AssociationImpl <em>Association</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.AssociationImpl
		 * @see BONModel.impl.BONModelPackageImpl#getAssociation()
		 * @generated
		 */
		EClass ASSOCIATION = eINSTANCE.getAssociation();

		/**
		 * The meta object literal for the '{@link BONModel.impl.MessageImpl <em>Message</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.MessageImpl
		 * @see BONModel.impl.BONModelPackageImpl#getMessage()
		 * @generated
		 */
		EClass MESSAGE = eINSTANCE.getMessage();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ClusterImpl <em>Cluster</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ClusterImpl
		 * @see BONModel.impl.BONModelPackageImpl#getCluster()
		 * @generated
		 */
		EClass CLUSTER = eINSTANCE.getCluster();

		/**
		 * The meta object literal for the '<em><b>Contents</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLUSTER__CONTENTS = eINSTANCE.getCluster_Contents();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ClassImpl <em>Class</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ClassImpl
		 * @see BONModel.impl.BONModelPackageImpl#getClass_()
		 * @generated
		 */
		EClass CLASS = eINSTANCE.getClass_();

		/**
		 * The meta object literal for the '<em><b>Calls In Invariants</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__CALLS_IN_INVARIANTS = eINSTANCE.getClass_CallsInInvariants();

		/**
		 * The meta object literal for the '<em><b>Features</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__FEATURES = eINSTANCE.getClass_Features();

		/**
		 * The meta object literal for the '<em><b>Client Features</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__CLIENT_FEATURES = eINSTANCE.getClass_ClientFeatures();

		/**
		 * The meta object literal for the '<em><b>Renamings</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__RENAMINGS = eINSTANCE.getClass_Renamings();

		/**
		 * The meta object literal for the '<em><b>Rename Class Parents</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__RENAME_CLASS_PARENTS = eINSTANCE.getClass_RenameClassParents();

		/**
		 * The meta object literal for the '<em><b>Is Deferred</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__IS_DEFERRED = eINSTANCE.getClass_IsDeferred();

		/**
		 * The meta object literal for the '<em><b>Is Effective</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__IS_EFFECTIVE = eINSTANCE.getClass_IsEffective();

		/**
		 * The meta object literal for the '<em><b>Is Persistent</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__IS_PERSISTENT = eINSTANCE.getClass_IsPersistent();

		/**
		 * The meta object literal for the '<em><b>Is External</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__IS_EXTERNAL = eINSTANCE.getClass_IsExternal();

		/**
		 * The meta object literal for the '<em><b>Is Root</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__IS_ROOT = eINSTANCE.getClass_IsRoot();

		/**
		 * The meta object literal for the '<em><b>Redefined</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__REDEFINED = eINSTANCE.getClass_Redefined();

		/**
		 * The meta object literal for the '<em><b>All Names</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__ALL_NAMES = eINSTANCE.getClass_AllNames();

		/**
		 * The meta object literal for the '<em><b>Invariant</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__INVARIANT = eINSTANCE.getClass_Invariant();

		/**
		 * The meta object literal for the '{@link BONModel.impl.CallImpl <em>Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.CallImpl
		 * @see BONModel.impl.BONModelPackageImpl#getCall()
		 * @generated
		 */
		EClass CALL = eINSTANCE.getCall();

		/**
		 * The meta object literal for the '<em><b>Arguments</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CALL__ARGUMENTS = eINSTANCE.getCall_Arguments();

		/**
		 * The meta object literal for the '<em><b>Feature</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CALL__FEATURE = eINSTANCE.getCall_Feature();

		/**
		 * The meta object literal for the '<em><b>Entity</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CALL__ENTITY = eINSTANCE.getCall_Entity();

		/**
		 * The meta object literal for the '{@link BONModel.impl.FeatureImpl <em>Feature</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.FeatureImpl
		 * @see BONModel.impl.BONModelPackageImpl#getFeature()
		 * @generated
		 */
		EClass FEATURE = eINSTANCE.getFeature();

		/**
		 * The meta object literal for the '<em><b>Is Deferred</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__IS_DEFERRED = eINSTANCE.getFeature_IsDeferred();

		/**
		 * The meta object literal for the '<em><b>Is Effective</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__IS_EFFECTIVE = eINSTANCE.getFeature_IsEffective();

		/**
		 * The meta object literal for the '<em><b>Is Redefined</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__IS_REDEFINED = eINSTANCE.getFeature_IsRedefined();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__NAME = eINSTANCE.getFeature_Name();

		/**
		 * The meta object literal for the '<em><b>Comment</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__COMMENT = eINSTANCE.getFeature_Comment();

		/**
		 * The meta object literal for the '<em><b>Accessors</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__ACCESSORS = eINSTANCE.getFeature_Accessors();

		/**
		 * The meta object literal for the '<em><b>Parameters</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__PARAMETERS = eINSTANCE.getFeature_Parameters();

		/**
		 * The meta object literal for the '<em><b>Pre Condition String</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__PRE_CONDITION_STRING = eINSTANCE.getFeature_PreConditionString();

		/**
		 * The meta object literal for the '<em><b>Post Condition String</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__POST_CONDITION_STRING = eINSTANCE.getFeature_PostConditionString();

		/**
		 * The meta object literal for the '<em><b>Calls In Precondition</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__CALLS_IN_PRECONDITION = eINSTANCE.getFeature_CallsInPrecondition();

		/**
		 * The meta object literal for the '<em><b>Calls In Postcondition</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__CALLS_IN_POSTCONDITION = eINSTANCE.getFeature_CallsInPostcondition();

		/**
		 * The meta object literal for the '<em><b>Frame</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__FRAME = eINSTANCE.getFeature_Frame();

		/**
		 * The meta object literal for the '<em><b>Post Condition</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__POST_CONDITION = eINSTANCE.getFeature_PostCondition();

		/**
		 * The meta object literal for the '<em><b>Pre Condition</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FEATURE__PRE_CONDITION = eINSTANCE.getFeature_PreCondition();

		/**
		 * The meta object literal for the '{@link BONModel.impl.RenamingImpl <em>Renaming</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.RenamingImpl
		 * @see BONModel.impl.BONModelPackageImpl#getRenaming()
		 * @generated
		 */
		EClass RENAMING = eINSTANCE.getRenaming();

		/**
		 * The meta object literal for the '{@link BONModel.impl.DynamicAbstractionImpl <em>Dynamic Abstraction</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.DynamicAbstractionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getDynamicAbstraction()
		 * @generated
		 */
		EClass DYNAMIC_ABSTRACTION = eINSTANCE.getDynamicAbstraction();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ObjectImpl <em>Object</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ObjectImpl
		 * @see BONModel.impl.BONModelPackageImpl#getObject()
		 * @generated
		 */
		EClass OBJECT = eINSTANCE.getObject();

		/**
		 * The meta object literal for the '<em><b>Class</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OBJECT__CLASS = eINSTANCE.getObject_Class();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ObjectClusterImpl <em>Object Cluster</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ObjectClusterImpl
		 * @see BONModel.impl.BONModelPackageImpl#getObjectCluster()
		 * @generated
		 */
		EClass OBJECT_CLUSTER = eINSTANCE.getObjectCluster();

		/**
		 * The meta object literal for the '<em><b>Contents</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OBJECT_CLUSTER__CONTENTS = eINSTANCE.getObjectCluster_Contents();

		/**
		 * The meta object literal for the '{@link BONModel.impl.CommandImpl <em>Command</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.CommandImpl
		 * @see BONModel.impl.BONModelPackageImpl#getCommand()
		 * @generated
		 */
		EClass COMMAND = eINSTANCE.getCommand();

		/**
		 * The meta object literal for the '{@link BONModel.impl.QueryImpl <em>Query</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.QueryImpl
		 * @see BONModel.impl.BONModelPackageImpl#getQuery()
		 * @generated
		 */
		EClass QUERY = eINSTANCE.getQuery();

		/**
		 * The meta object literal for the '<em><b>Result</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference QUERY__RESULT = eINSTANCE.getQuery_Result();

		/**
		 * The meta object literal for the '<em><b>No Contract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute QUERY__NO_CONTRACT = eINSTANCE.getQuery_NoContract();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ParameterImpl <em>Parameter</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ParameterImpl
		 * @see BONModel.impl.BONModelPackageImpl#getParameter()
		 * @generated
		 */
		EClass PARAMETER = eINSTANCE.getParameter();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PARAMETER__NAME = eINSTANCE.getParameter_Name();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PARAMETER__TYPE = eINSTANCE.getParameter_Type();

		/**
		 * The meta object literal for the '{@link BONModel.impl.DirectCallImpl <em>Direct Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.DirectCallImpl
		 * @see BONModel.impl.BONModelPackageImpl#getDirectCall()
		 * @generated
		 */
		EClass DIRECT_CALL = eINSTANCE.getDirectCall();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ChainedCallImpl <em>Chained Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ChainedCallImpl
		 * @see BONModel.impl.BONModelPackageImpl#getChainedCall()
		 * @generated
		 */
		EClass CHAINED_CALL = eINSTANCE.getChainedCall();

		/**
		 * The meta object literal for the '<em><b>Chain</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CHAINED_CALL__CHAIN = eINSTANCE.getChainedCall_Chain();

		/**
		 * The meta object literal for the '{@link BONModel.impl.ExpressionImpl <em>Expression</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.ExpressionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getExpression()
		 * @generated
		 */
		EClass EXPRESSION = eINSTANCE.getExpression();

		/**
		 * The meta object literal for the '<em><b>Result Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EXPRESSION__RESULT_TYPE = eINSTANCE.getExpression_ResultType();

		/**
		 * The meta object literal for the '<em><b>Contents</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute EXPRESSION__CONTENTS = eINSTANCE.getExpression_Contents();

		/**
		 * The meta object literal for the '{@link BONModel.impl.BooleanExpressionImpl <em>Boolean Expression</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.BooleanExpressionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getBooleanExpression()
		 * @generated
		 */
		EClass BOOLEAN_EXPRESSION = eINSTANCE.getBooleanExpression();

		/**
		 * The meta object literal for the '{@link BONModel.impl.AssertionImpl <em>Assertion</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.AssertionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getAssertion()
		 * @generated
		 */
		EClass ASSERTION = eINSTANCE.getAssertion();

		/**
		 * The meta object literal for the '{@link BONModel.impl.SingleStateAssertionImpl <em>Single State Assertion</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.SingleStateAssertionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getSingleStateAssertion()
		 * @generated
		 */
		EClass SINGLE_STATE_ASSERTION = eINSTANCE.getSingleStateAssertion();

		/**
		 * The meta object literal for the '{@link BONModel.impl.DoubleStateAssertionImpl <em>Double State Assertion</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.DoubleStateAssertionImpl
		 * @see BONModel.impl.BONModelPackageImpl#getDoubleStateAssertion()
		 * @generated
		 */
		EClass DOUBLE_STATE_ASSERTION = eINSTANCE.getDoubleStateAssertion();

		/**
		 * The meta object literal for the '{@link BONModel.impl.EntityImpl <em>Entity</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.impl.EntityImpl
		 * @see BONModel.impl.BONModelPackageImpl#getEntity()
		 * @generated
		 */
		EClass ENTITY = eINSTANCE.getEntity();

		/**
		 * The meta object literal for the '{@link BONModel.RelationshipType <em>Relationship Type</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see BONModel.RelationshipType
		 * @see BONModel.impl.BONModelPackageImpl#getRelationshipType()
		 * @generated
		 */
		EEnum RELATIONSHIP_TYPE = eINSTANCE.getRelationshipType();

	}

} //BONModelPackage

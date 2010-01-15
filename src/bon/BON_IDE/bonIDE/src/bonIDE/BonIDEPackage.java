/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
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
	 * The number of structural features of the '<em>Model</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL_FEATURE_COUNT = 1;

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
	 * The feature id for the '<em><b>Parents</b></em>' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS__PARENTS = STATIC_ABSTRACTION_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>BON Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BON_CLASS_FEATURE_COUNT = STATIC_ABSTRACTION_FEATURE_COUNT + 4;

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
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE__NAME = 0;

	/**
	 * The number of structural features of the '<em>Feature</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FEATURE_FEATURE_COUNT = 1;


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
	 * Returns the meta object for the attribute list '{@link bonIDE.BONClass#getParents <em>Parents</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute list '<em>Parents</em>'.
	 * @see bonIDE.BONClass#getParents()
	 * @see #getBONClass()
	 * @generated
	 */
	EAttribute getBONClass_Parents();

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
	 * Returns the meta object for the attribute '{@link bonIDE.Feature#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see bonIDE.Feature#getName()
	 * @see #getFeature()
	 * @generated
	 */
	EAttribute getFeature_Name();

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
		 * The meta object literal for the '<em><b>Parents</b></em>' attribute list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BON_CLASS__PARENTS = eINSTANCE.getBONClass_Parents();

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
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute FEATURE__NAME = eINSTANCE.getFeature_Name();

	}

} //BonIDEPackage

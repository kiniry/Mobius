/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package SimpleGMF;

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
 * @see SimpleGMF.SimpleGMFFactory
 * @model kind="package"
 * @generated
 */
public interface SimpleGMFPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "SimpleGMF";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "SimpleGMF.com";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "SimpleGMF";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	SimpleGMFPackage eINSTANCE = SimpleGMF.impl.SimpleGMFPackageImpl.init();

	/**
	 * The meta object id for the '{@link SimpleGMF.impl.SimpleClassImpl <em>Simple Class</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see SimpleGMF.impl.SimpleClassImpl
	 * @see SimpleGMF.impl.SimpleGMFPackageImpl#getSimpleClass()
	 * @generated
	 */
	int SIMPLE_CLASS = 0;

	/**
	 * The feature id for the '<em><b>Class Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SIMPLE_CLASS__CLASS_NAME = 0;

	/**
	 * The number of structural features of the '<em>Simple Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SIMPLE_CLASS_FEATURE_COUNT = 1;

	/**
	 * The meta object id for the '{@link SimpleGMF.impl.ModelImpl <em>Model</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see SimpleGMF.impl.ModelImpl
	 * @see SimpleGMF.impl.SimpleGMFPackageImpl#getModel()
	 * @generated
	 */
	int MODEL = 1;

	/**
	 * The feature id for the '<em><b>Classes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL__CLASSES = 0;

	/**
	 * The number of structural features of the '<em>Model</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MODEL_FEATURE_COUNT = 1;


	/**
	 * Returns the meta object for class '{@link SimpleGMF.SimpleClass <em>Simple Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Simple Class</em>'.
	 * @see SimpleGMF.SimpleClass
	 * @generated
	 */
	EClass getSimpleClass();

	/**
	 * Returns the meta object for the attribute '{@link SimpleGMF.SimpleClass#getClassName <em>Class Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Class Name</em>'.
	 * @see SimpleGMF.SimpleClass#getClassName()
	 * @see #getSimpleClass()
	 * @generated
	 */
	EAttribute getSimpleClass_ClassName();

	/**
	 * Returns the meta object for class '{@link SimpleGMF.Model <em>Model</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Model</em>'.
	 * @see SimpleGMF.Model
	 * @generated
	 */
	EClass getModel();

	/**
	 * Returns the meta object for the containment reference list '{@link SimpleGMF.Model#getClasses <em>Classes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Classes</em>'.
	 * @see SimpleGMF.Model#getClasses()
	 * @see #getModel()
	 * @generated
	 */
	EReference getModel_Classes();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	SimpleGMFFactory getSimpleGMFFactory();

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
		 * The meta object literal for the '{@link SimpleGMF.impl.SimpleClassImpl <em>Simple Class</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see SimpleGMF.impl.SimpleClassImpl
		 * @see SimpleGMF.impl.SimpleGMFPackageImpl#getSimpleClass()
		 * @generated
		 */
		EClass SIMPLE_CLASS = eINSTANCE.getSimpleClass();

		/**
		 * The meta object literal for the '<em><b>Class Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute SIMPLE_CLASS__CLASS_NAME = eINSTANCE.getSimpleClass_ClassName();

		/**
		 * The meta object literal for the '{@link SimpleGMF.impl.ModelImpl <em>Model</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see SimpleGMF.impl.ModelImpl
		 * @see SimpleGMF.impl.SimpleGMFPackageImpl#getModel()
		 * @generated
		 */
		EClass MODEL = eINSTANCE.getModel();

		/**
		 * The meta object literal for the '<em><b>Classes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MODEL__CLASSES = eINSTANCE.getModel_Classes();

	}

} //SimpleGMFPackage

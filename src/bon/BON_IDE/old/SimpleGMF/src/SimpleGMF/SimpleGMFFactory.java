/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package SimpleGMF;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see SimpleGMF.SimpleGMFPackage
 * @generated
 */
public interface SimpleGMFFactory extends EFactory {
	/**
	 * The singleton instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	SimpleGMFFactory eINSTANCE = SimpleGMF.impl.SimpleGMFFactoryImpl.init();

	/**
	 * Returns a new object of class '<em>Simple Class</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Simple Class</em>'.
	 * @generated
	 */
	SimpleClass createSimpleClass();

	/**
	 * Returns a new object of class '<em>Model</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Model</em>'.
	 * @generated
	 */
	Model createModel();

	/**
	 * Returns the package supported by this factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the package supported by this factory.
	 * @generated
	 */
	SimpleGMFPackage getSimpleGMFPackage();

} //SimpleGMFFactory

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Feature Argument</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.FeatureArgument#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.FeatureArgument#getType <em>Type</em>}</li>
 *   <li>{@link bonIDE.FeatureArgument#getContainerType <em>Container Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getFeatureArgument()
 * @model
 * @generated
 */
public interface FeatureArgument extends EObject {
	/**
	 * Returns the value of the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Name</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Name</em>' attribute.
	 * @see #setName(String)
	 * @see bonIDE.BonIDEPackage#getFeatureArgument_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link bonIDE.FeatureArgument#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

	/**
	 * Returns the value of the '<em><b>Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Type</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Type</em>' attribute.
	 * @see #setType(String)
	 * @see bonIDE.BonIDEPackage#getFeatureArgument_Type()
	 * @model
	 * @generated
	 */
	String getType();

	/**
	 * Sets the value of the '{@link bonIDE.FeatureArgument#getType <em>Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Type</em>' attribute.
	 * @see #getType()
	 * @generated
	 */
	void setType(String value);

	/**
	 * Returns the value of the '<em><b>Container Type</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Container Type</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Container Type</em>' attribute.
	 * @see #setContainerType(String)
	 * @see bonIDE.BonIDEPackage#getFeatureArgument_ContainerType()
	 * @model
	 * @generated
	 */
	String getContainerType();

	/**
	 * Sets the value of the '{@link bonIDE.FeatureArgument#getContainerType <em>Container Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Container Type</em>' attribute.
	 * @see #getContainerType()
	 * @generated
	 */
	void setContainerType(String value);

} // FeatureArgument

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>BON Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.BONClass#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.BONClass#getFeatures <em>Features</em>}</li>
 *   <li>{@link bonIDE.BONClass#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link bonIDE.BONClass#getParents <em>Parents</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getBONClass()
 * @model
 * @generated
 */
public interface BONClass extends StaticAbstraction {
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
	 * @see bonIDE.BonIDEPackage#getBONClass_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

	/**
	 * Returns the value of the '<em><b>Features</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.Feature}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Features</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Features</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getBONClass_Features()
	 * @model containment="true"
	 * @generated
	 */
	EList<Feature> getFeatures();

	/**
	 * Returns the value of the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Deferred</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Deferred</em>' attribute.
	 * @see #setIsDeferred(boolean)
	 * @see bonIDE.BonIDEPackage#getBONClass_IsDeferred()
	 * @model
	 * @generated
	 */
	boolean isIsDeferred();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#isIsDeferred <em>Is Deferred</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Deferred</em>' attribute.
	 * @see #isIsDeferred()
	 * @generated
	 */
	void setIsDeferred(boolean value);

	/**
	 * Returns the value of the '<em><b>Parents</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.String}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Parents</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parents</em>' attribute list.
	 * @see bonIDE.BonIDEPackage#getBONClass_Parents()
	 * @model
	 * @generated
	 */
	EList<String> getParents();

} // BONClass

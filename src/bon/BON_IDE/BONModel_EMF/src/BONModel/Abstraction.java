/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstraction</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Abstraction#getRelationships <em>Relationships</em>}</li>
 *   <li>{@link BONModel.Abstraction#getContains <em>Contains</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getAbstraction()
 * @model abstract="true"
 * @generated
 */
public interface Abstraction extends EObject {
	/**
	 * Returns the value of the '<em><b>Relationships</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Relationship}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Relationships</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Relationships</em>' reference list.
	 * @see BONModel.BONModelPackage#getAbstraction_Relationships()
	 * @model
	 * @generated
	 */
	EList<Relationship> getRelationships();

	/**
	 * Returns the value of the '<em><b>Contains</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Abstraction}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Contains</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Contains</em>' reference list.
	 * @see BONModel.BONModelPackage#getAbstraction_Contains()
	 * @model
	 * @generated
	 */
	EList<Abstraction> getContains();

} // Abstraction

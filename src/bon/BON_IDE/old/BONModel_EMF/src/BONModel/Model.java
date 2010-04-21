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
 * A representation of the model object '<em><b>Model</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Model#getClosure <em>Closure</em>}</li>
 *   <li>{@link BONModel.Model#getAbstractions <em>Abstractions</em>}</li>
 *   <li>{@link BONModel.Model#getRelationships <em>Relationships</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getModel()
 * @model
 * @generated
 */
public interface Model extends EObject {
	/**
	 * Returns the value of the '<em><b>Relationships</b></em>' containment reference list.
	 * The list contents are of type {@link BONModel.Relationship}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Relationships</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Relationships</em>' containment reference list.
	 * @see BONModel.BONModelPackage#getModel_Relationships()
	 * @model containment="true"
	 * @generated
	 */
	EList<Relationship> getRelationships();

	/**
	 * Returns the value of the '<em><b>Closure</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Inheritance}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Closure</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Closure</em>' reference list.
	 * @see BONModel.BONModelPackage#getModel_Closure()
	 * @model
	 * @generated
	 */
	EList<Inheritance> getClosure();

	/**
	 * Returns the value of the '<em><b>Abstractions</b></em>' containment reference list.
	 * The list contents are of type {@link BONModel.Abstraction}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Abstractions</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Abstractions</em>' containment reference list.
	 * @see BONModel.BONModelPackage#getModel_Abstractions()
	 * @model containment="true"
	 * @generated
	 */
	EList<Abstraction> getAbstractions();

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model
	 * @generated
	 */
	Boolean covariant(Feature featureOne, Feature featureTwo);

} // Model

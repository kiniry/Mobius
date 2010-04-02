/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

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
 *   <li>{@link bonIDE.Model#getAbstractions <em>Abstractions</em>}</li>
 *   <li>{@link bonIDE.Model#getRelationships <em>Relationships</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getModel()
 * @model
 * @generated
 */
public interface Model extends EObject {
	/**
	 * Returns the value of the '<em><b>Abstractions</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.Abstraction}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Abstractions</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Abstractions</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getModel_Abstractions()
	 * @model containment="true"
	 * @generated
	 */
	EList<Abstraction> getAbstractions();

	/**
	 * Returns the value of the '<em><b>Relationships</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.StaticRelationship}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Relationships</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Relationships</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getModel_Relationships()
	 * @model containment="true"
	 * @generated
	 */
	EList<StaticRelationship> getRelationships();

} // Model

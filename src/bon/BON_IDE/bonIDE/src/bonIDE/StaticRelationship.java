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
 * A representation of the model object '<em><b>Static Relationship</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.StaticRelationship#getType <em>Type</em>}</li>
 *   <li>{@link bonIDE.StaticRelationship#getSource <em>Source</em>}</li>
 *   <li>{@link bonIDE.StaticRelationship#getTarget <em>Target</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getStaticRelationship()
 * @model
 * @generated
 */
public interface StaticRelationship extends EObject {
	/**
	 * Returns the value of the '<em><b>Type</b></em>' attribute.
	 * The literals are from the enumeration {@link bonIDE.RelationshipType}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Type</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Type</em>' attribute.
	 * @see bonIDE.RelationshipType
	 * @see #setType(RelationshipType)
	 * @see bonIDE.BonIDEPackage#getStaticRelationship_Type()
	 * @model
	 * @generated
	 */
	RelationshipType getType();

	/**
	 * Sets the value of the '{@link bonIDE.StaticRelationship#getType <em>Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Type</em>' attribute.
	 * @see bonIDE.RelationshipType
	 * @see #getType()
	 * @generated
	 */
	void setType(RelationshipType value);

	/**
	 * Returns the value of the '<em><b>Source</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Source</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Source</em>' reference.
	 * @see #setSource(Abstraction)
	 * @see bonIDE.BonIDEPackage#getStaticRelationship_Source()
	 * @model
	 * @generated
	 */
	Abstraction getSource();

	/**
	 * Sets the value of the '{@link bonIDE.StaticRelationship#getSource <em>Source</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Source</em>' reference.
	 * @see #getSource()
	 * @generated
	 */
	void setSource(Abstraction value);

	/**
	 * Returns the value of the '<em><b>Target</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Target</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Target</em>' reference.
	 * @see #setTarget(Abstraction)
	 * @see bonIDE.BonIDEPackage#getStaticRelationship_Target()
	 * @model
	 * @generated
	 */
	Abstraction getTarget();

	/**
	 * Sets the value of the '{@link bonIDE.StaticRelationship#getTarget <em>Target</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Target</em>' reference.
	 * @see #getTarget()
	 * @generated
	 */
	void setTarget(Abstraction value);

} // StaticRelationship

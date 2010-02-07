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
 * A representation of the model object '<em><b>Feature</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.Feature#getNames <em>Names</em>}</li>
 *   <li>{@link bonIDE.Feature#getModifier <em>Modifier</em>}</li>
 *   <li>{@link bonIDE.Feature#getType <em>Type</em>}</li>
 *   <li>{@link bonIDE.Feature#getComment <em>Comment</em>}</li>
 *   <li>{@link bonIDE.Feature#getArguments <em>Arguments</em>}</li>
 *   <li>{@link bonIDE.Feature#getPostConditions <em>Post Conditions</em>}</li>
 *   <li>{@link bonIDE.Feature#getPreConditions <em>Pre Conditions</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getFeature()
 * @model
 * @generated
 */
public interface Feature extends EObject {
	/**
	 * Returns the value of the '<em><b>Names</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.String}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Names</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Names</em>' attribute list.
	 * @see bonIDE.BonIDEPackage#getFeature_Names()
	 * @model
	 * @generated
	 */
	EList<String> getNames();

	/**
	 * Returns the value of the '<em><b>Modifier</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Modifier</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Modifier</em>' attribute.
	 * @see #setModifier(String)
	 * @see bonIDE.BonIDEPackage#getFeature_Modifier()
	 * @model
	 * @generated
	 */
	String getModifier();

	/**
	 * Sets the value of the '{@link bonIDE.Feature#getModifier <em>Modifier</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Modifier</em>' attribute.
	 * @see #getModifier()
	 * @generated
	 */
	void setModifier(String value);

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
	 * @see bonIDE.BonIDEPackage#getFeature_Type()
	 * @model
	 * @generated
	 */
	String getType();

	/**
	 * Sets the value of the '{@link bonIDE.Feature#getType <em>Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Type</em>' attribute.
	 * @see #getType()
	 * @generated
	 */
	void setType(String value);

	/**
	 * Returns the value of the '<em><b>Comment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Comment</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Comment</em>' attribute.
	 * @see #setComment(String)
	 * @see bonIDE.BonIDEPackage#getFeature_Comment()
	 * @model
	 * @generated
	 */
	String getComment();

	/**
	 * Sets the value of the '{@link bonIDE.Feature#getComment <em>Comment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Comment</em>' attribute.
	 * @see #getComment()
	 * @generated
	 */
	void setComment(String value);

	/**
	 * Returns the value of the '<em><b>Arguments</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.FeatureArgument}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Arguments</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Arguments</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getFeature_Arguments()
	 * @model containment="true"
	 * @generated
	 */
	EList<FeatureArgument> getArguments();

	/**
	 * Returns the value of the '<em><b>Post Conditions</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.PostCondition}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Post Conditions</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Post Conditions</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getFeature_PostConditions()
	 * @model containment="true"
	 * @generated
	 */
	EList<PostCondition> getPostConditions();

	/**
	 * Returns the value of the '<em><b>Pre Conditions</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.PreCondition}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Pre Conditions</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Pre Conditions</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getFeature_PreConditions()
	 * @model containment="true"
	 * @generated
	 */
	EList<PreCondition> getPreConditions();

} // Feature

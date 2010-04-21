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
 * A representation of the model object '<em><b>Feature</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Feature#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link BONModel.Feature#isIsEffective <em>Is Effective</em>}</li>
 *   <li>{@link BONModel.Feature#isIsRedefined <em>Is Redefined</em>}</li>
 *   <li>{@link BONModel.Feature#getName <em>Name</em>}</li>
 *   <li>{@link BONModel.Feature#getComment <em>Comment</em>}</li>
 *   <li>{@link BONModel.Feature#getAccessors <em>Accessors</em>}</li>
 *   <li>{@link BONModel.Feature#getCallsInPrecondition <em>Calls In Precondition</em>}</li>
 *   <li>{@link BONModel.Feature#getCallsInPostcondition <em>Calls In Postcondition</em>}</li>
 *   <li>{@link BONModel.Feature#getFrame <em>Frame</em>}</li>
 *   <li>{@link BONModel.Feature#getPostCondition <em>Post Condition</em>}</li>
 *   <li>{@link BONModel.Feature#getPreCondition <em>Pre Condition</em>}</li>
 *   <li>{@link BONModel.Feature#getParameters <em>Parameters</em>}</li>
 *   <li>{@link BONModel.Feature#getPreConditionString <em>Pre Condition String</em>}</li>
 *   <li>{@link BONModel.Feature#getPostConditionString <em>Post Condition String</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getFeature()
 * @model abstract="true"
 * @generated
 */
public interface Feature extends EObject {
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
	 * @see BONModel.BONModelPackage#getFeature_IsDeferred()
	 * @model
	 * @generated
	 */
	boolean isIsDeferred();

	/**
	 * Sets the value of the '{@link BONModel.Feature#isIsDeferred <em>Is Deferred</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Deferred</em>' attribute.
	 * @see #isIsDeferred()
	 * @generated
	 */
	void setIsDeferred(boolean value);

	/**
	 * Returns the value of the '<em><b>Is Effective</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Effective</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Effective</em>' attribute.
	 * @see #setIsEffective(boolean)
	 * @see BONModel.BONModelPackage#getFeature_IsEffective()
	 * @model
	 * @generated
	 */
	boolean isIsEffective();

	/**
	 * Sets the value of the '{@link BONModel.Feature#isIsEffective <em>Is Effective</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Effective</em>' attribute.
	 * @see #isIsEffective()
	 * @generated
	 */
	void setIsEffective(boolean value);

	/**
	 * Returns the value of the '<em><b>Is Redefined</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Redefined</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Redefined</em>' attribute.
	 * @see #setIsRedefined(boolean)
	 * @see BONModel.BONModelPackage#getFeature_IsRedefined()
	 * @model
	 * @generated
	 */
	boolean isIsRedefined();

	/**
	 * Sets the value of the '{@link BONModel.Feature#isIsRedefined <em>Is Redefined</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Redefined</em>' attribute.
	 * @see #isIsRedefined()
	 * @generated
	 */
	void setIsRedefined(boolean value);

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
	 * @see BONModel.BONModelPackage#getFeature_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

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
	 * @see BONModel.BONModelPackage#getFeature_Comment()
	 * @model
	 * @generated
	 */
	String getComment();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getComment <em>Comment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Comment</em>' attribute.
	 * @see #getComment()
	 * @generated
	 */
	void setComment(String value);

	/**
	 * Returns the value of the '<em><b>Accessors</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Class}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Accessors</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Accessors</em>' reference list.
	 * @see BONModel.BONModelPackage#getFeature_Accessors()
	 * @model
	 * @generated
	 */
	EList<BONModel.Class> getAccessors();

	/**
	 * Returns the value of the '<em><b>Parameters</b></em>' containment reference list.
	 * The list contents are of type {@link BONModel.Parameter}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Parameters</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parameters</em>' containment reference list.
	 * @see BONModel.BONModelPackage#getFeature_Parameters()
	 * @model containment="true"
	 * @generated
	 */
	EList<Parameter> getParameters();

	/**
	 * Returns the value of the '<em><b>Pre Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Pre Condition String</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Pre Condition String</em>' attribute.
	 * @see #setPreConditionString(String)
	 * @see BONModel.BONModelPackage#getFeature_PreConditionString()
	 * @model
	 * @generated
	 */
	String getPreConditionString();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getPreConditionString <em>Pre Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Pre Condition String</em>' attribute.
	 * @see #getPreConditionString()
	 * @generated
	 */
	void setPreConditionString(String value);

	/**
	 * Returns the value of the '<em><b>Post Condition String</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Post Condition String</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Post Condition String</em>' attribute.
	 * @see #setPostConditionString(String)
	 * @see BONModel.BONModelPackage#getFeature_PostConditionString()
	 * @model
	 * @generated
	 */
	String getPostConditionString();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getPostConditionString <em>Post Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Post Condition String</em>' attribute.
	 * @see #getPostConditionString()
	 * @generated
	 */
	void setPostConditionString(String value);

	/**
	 * Returns the value of the '<em><b>Calls In Precondition</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Call}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Calls In Precondition</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Calls In Precondition</em>' reference list.
	 * @see BONModel.BONModelPackage#getFeature_CallsInPrecondition()
	 * @model
	 * @generated
	 */
	EList<Call> getCallsInPrecondition();

	/**
	 * Returns the value of the '<em><b>Calls In Postcondition</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Call}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Calls In Postcondition</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Calls In Postcondition</em>' reference list.
	 * @see BONModel.BONModelPackage#getFeature_CallsInPostcondition()
	 * @model
	 * @generated
	 */
	EList<Call> getCallsInPostcondition();

	/**
	 * Returns the value of the '<em><b>Frame</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Query}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Frame</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Frame</em>' reference list.
	 * @see BONModel.BONModelPackage#getFeature_Frame()
	 * @model
	 * @generated
	 */
	EList<Query> getFrame();

	/**
	 * Returns the value of the '<em><b>Post Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Post Condition</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Post Condition</em>' reference.
	 * @see #setPostCondition(DoubleStateAssertion)
	 * @see BONModel.BONModelPackage#getFeature_PostCondition()
	 * @model
	 * @generated
	 */
	DoubleStateAssertion getPostCondition();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getPostCondition <em>Post Condition</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Post Condition</em>' reference.
	 * @see #getPostCondition()
	 * @generated
	 */
	void setPostCondition(DoubleStateAssertion value);

	/**
	 * Returns the value of the '<em><b>Pre Condition</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Pre Condition</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Pre Condition</em>' reference.
	 * @see #setPreCondition(SingleStateAssertion)
	 * @see BONModel.BONModelPackage#getFeature_PreCondition()
	 * @model
	 * @generated
	 */
	SingleStateAssertion getPreCondition();

	/**
	 * Sets the value of the '{@link BONModel.Feature#getPreCondition <em>Pre Condition</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Pre Condition</em>' reference.
	 * @see #getPreCondition()
	 * @generated
	 */
	void setPreCondition(SingleStateAssertion value);

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @model
	 * @generated
	 */
	void rename(String newName);

} // Feature

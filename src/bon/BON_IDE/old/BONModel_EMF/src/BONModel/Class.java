/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Class#getCallsInInvariants <em>Calls In Invariants</em>}</li>
 *   <li>{@link BONModel.Class#getClientFeatures <em>Client Features</em>}</li>
 *   <li>{@link BONModel.Class#getRenamings <em>Renamings</em>}</li>
 *   <li>{@link BONModel.Class#getRenameClassParents <em>Rename Class Parents</em>}</li>
 *   <li>{@link BONModel.Class#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link BONModel.Class#isIsEffective <em>Is Effective</em>}</li>
 *   <li>{@link BONModel.Class#isIsPersistent <em>Is Persistent</em>}</li>
 *   <li>{@link BONModel.Class#isIsExternal <em>Is External</em>}</li>
 *   <li>{@link BONModel.Class#isIsRoot <em>Is Root</em>}</li>
 *   <li>{@link BONModel.Class#getRedefined <em>Redefined</em>}</li>
 *   <li>{@link BONModel.Class#getAllNames <em>All Names</em>}</li>
 *   <li>{@link BONModel.Class#getInvariant <em>Invariant</em>}</li>
 *   <li>{@link BONModel.Class#getFeatures <em>Features</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getClass_()
 * @model
 * @generated
 */
public interface Class extends StaticAbstraction {
	/**
	 * Returns the value of the '<em><b>Calls In Invariants</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Call}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Calls In Invariants</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Calls In Invariants</em>' reference list.
	 * @see BONModel.BONModelPackage#getClass_CallsInInvariants()
	 * @model
	 * @generated
	 */
	EList<Call> getCallsInInvariants();

	/**
	 * Returns the value of the '<em><b>Features</b></em>' containment reference list.
	 * The list contents are of type {@link BONModel.Feature}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Features</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Features</em>' containment reference list.
	 * @see BONModel.BONModelPackage#getClass_Features()
	 * @model containment="true"
	 * @generated
	 */
	EList<Feature> getFeatures();

	/**
	 * Returns the value of the '<em><b>Client Features</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Feature}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Client Features</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Client Features</em>' reference list.
	 * @see BONModel.BONModelPackage#getClass_ClientFeatures()
	 * @model
	 * @generated
	 */
	EList<Feature> getClientFeatures();

	/**
	 * Returns the value of the '<em><b>Renamings</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Renaming}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Renamings</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Renamings</em>' reference list.
	 * @see BONModel.BONModelPackage#getClass_Renamings()
	 * @model
	 * @generated
	 */
	EList<Renaming> getRenamings();

	/**
	 * Returns the value of the '<em><b>Rename Class Parents</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Class}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Rename Class Parents</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Rename Class Parents</em>' reference list.
	 * @see BONModel.BONModelPackage#getClass_RenameClassParents()
	 * @model
	 * @generated
	 */
	EList<Class> getRenameClassParents();

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
	 * @see BONModel.BONModelPackage#getClass_IsDeferred()
	 * @model
	 * @generated
	 */
	boolean isIsDeferred();

	/**
	 * Sets the value of the '{@link BONModel.Class#isIsDeferred <em>Is Deferred</em>}' attribute.
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
	 * @see BONModel.BONModelPackage#getClass_IsEffective()
	 * @model
	 * @generated
	 */
	boolean isIsEffective();

	/**
	 * Sets the value of the '{@link BONModel.Class#isIsEffective <em>Is Effective</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Effective</em>' attribute.
	 * @see #isIsEffective()
	 * @generated
	 */
	void setIsEffective(boolean value);

	/**
	 * Returns the value of the '<em><b>Is Persistent</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Persistent</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Persistent</em>' attribute.
	 * @see #setIsPersistent(boolean)
	 * @see BONModel.BONModelPackage#getClass_IsPersistent()
	 * @model
	 * @generated
	 */
	boolean isIsPersistent();

	/**
	 * Sets the value of the '{@link BONModel.Class#isIsPersistent <em>Is Persistent</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Persistent</em>' attribute.
	 * @see #isIsPersistent()
	 * @generated
	 */
	void setIsPersistent(boolean value);

	/**
	 * Returns the value of the '<em><b>Is External</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is External</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is External</em>' attribute.
	 * @see #setIsExternal(boolean)
	 * @see BONModel.BONModelPackage#getClass_IsExternal()
	 * @model
	 * @generated
	 */
	boolean isIsExternal();

	/**
	 * Sets the value of the '{@link BONModel.Class#isIsExternal <em>Is External</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is External</em>' attribute.
	 * @see #isIsExternal()
	 * @generated
	 */
	void setIsExternal(boolean value);

	/**
	 * Returns the value of the '<em><b>Is Root</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Root</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Root</em>' attribute.
	 * @see #setIsRoot(boolean)
	 * @see BONModel.BONModelPackage#getClass_IsRoot()
	 * @model
	 * @generated
	 */
	boolean isIsRoot();

	/**
	 * Sets the value of the '{@link BONModel.Class#isIsRoot <em>Is Root</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Root</em>' attribute.
	 * @see #isIsRoot()
	 * @generated
	 */
	void setIsRoot(boolean value);

	/**
	 * Returns the value of the '<em><b>Redefined</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Feature}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Redefined</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Redefined</em>' reference list.
	 * @see BONModel.BONModelPackage#getClass_Redefined()
	 * @model
	 * @generated
	 */
	EList<Feature> getRedefined();

	/**
	 * Returns the value of the '<em><b>All Names</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.String}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>All Names</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>All Names</em>' attribute list.
	 * @see BONModel.BONModelPackage#getClass_AllNames()
	 * @model
	 * @generated
	 */
	EList<String> getAllNames();

	/**
	 * Returns the value of the '<em><b>Invariant</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Invariant</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Invariant</em>' reference.
	 * @see #setInvariant(DoubleStateAssertion)
	 * @see BONModel.BONModelPackage#getClass_Invariant()
	 * @model
	 * @generated
	 */
	DoubleStateAssertion getInvariant();

	/**
	 * Sets the value of the '{@link BONModel.Class#getInvariant <em>Invariant</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Invariant</em>' reference.
	 * @see #getInvariant()
	 * @generated
	 */
	void setInvariant(DoubleStateAssertion value);

} // Class

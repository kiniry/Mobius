/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Object</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Object#getClass_ <em>Class</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getObject()
 * @model
 * @generated
 */
public interface Object extends DynamicAbstraction {
	/**
	 * Returns the value of the '<em><b>Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Class</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Class</em>' reference.
	 * @see #setClass(BONModel.Class)
	 * @see BONModel.BONModelPackage#getObject_Class()
	 * @model
	 * @generated
	 */
	BONModel.Class getClass_();

	/**
	 * Sets the value of the '{@link BONModel.Object#getClass_ <em>Class</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Class</em>' reference.
	 * @see #getClass_()
	 * @generated
	 */
	void setClass(BONModel.Class value);

} // Object

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Query</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Query#getResult <em>Result</em>}</li>
 *   <li>{@link BONModel.Query#isNoContract <em>No Contract</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getQuery()
 * @model
 * @generated
 */
public interface Query extends Feature {
	/**
	 * Returns the value of the '<em><b>Result</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Result</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Result</em>' reference.
	 * @see #setResult(BONModel.Class)
	 * @see BONModel.BONModelPackage#getQuery_Result()
	 * @model
	 * @generated
	 */
	BONModel.Class getResult();

	/**
	 * Sets the value of the '{@link BONModel.Query#getResult <em>Result</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Result</em>' reference.
	 * @see #getResult()
	 * @generated
	 */
	void setResult(BONModel.Class value);

	/**
	 * Returns the value of the '<em><b>No Contract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>No Contract</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>No Contract</em>' attribute.
	 * @see #setNoContract(boolean)
	 * @see BONModel.BONModelPackage#getQuery_NoContract()
	 * @model
	 * @generated
	 */
	boolean isNoContract();

	/**
	 * Sets the value of the '{@link BONModel.Query#isNoContract <em>No Contract</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>No Contract</em>' attribute.
	 * @see #isNoContract()
	 * @generated
	 */
	void setNoContract(boolean value);

} // Query

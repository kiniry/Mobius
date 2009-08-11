/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Chained Call</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.ChainedCall#getChain <em>Chain</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getChainedCall()
 * @model
 * @generated
 */
public interface ChainedCall extends Call {

	/**
	 * Returns the value of the '<em><b>Chain</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Chain</em>' reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Chain</em>' reference.
	 * @see #setChain(Call)
	 * @see BONModel.BONModelPackage#getChainedCall_Chain()
	 * @model
	 * @generated
	 */
	Call getChain();

	/**
	 * Sets the value of the '{@link BONModel.ChainedCall#getChain <em>Chain</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Chain</em>' reference.
	 * @see #getChain()
	 * @generated
	 */
	void setChain(Call value);
} // ChainedCall

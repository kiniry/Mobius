/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Client Supplier</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.ClientSupplier#getLabel <em>Label</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getClientSupplier()
 * @model abstract="true"
 * @generated
 */
public interface ClientSupplier extends StaticRelationship {
	/**
	 * Returns the value of the '<em><b>Label</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Label</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Label</em>' attribute.
	 * @see #setLabel(String)
	 * @see BONModel.BONModelPackage#getClientSupplier_Label()
	 * @model
	 * @generated
	 */
	String getLabel();

	/**
	 * Sets the value of the '{@link BONModel.ClientSupplier#getLabel <em>Label</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Label</em>' attribute.
	 * @see #getLabel()
	 * @generated
	 */
	void setLabel(String value);

} // ClientSupplier

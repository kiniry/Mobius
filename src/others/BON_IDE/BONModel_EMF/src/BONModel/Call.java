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
 * A representation of the model object '<em><b>Call</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Call#getArguments <em>Arguments</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getCall()
 * @model abstract="true"
 * @generated
 */
public interface Call extends EObject {
	/**
	 * Returns the value of the '<em><b>Arguments</b></em>' reference list.
	 * The list contents are of type {@link BONModel.Parameter}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Arguments</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Arguments</em>' reference list.
	 * @see BONModel.BONModelPackage#getCall_Arguments()
	 * @model
	 * @generated
	 */
	EList<Parameter> getArguments();

} // Call

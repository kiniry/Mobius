/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package SimpleGMF;

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
 *   <li>{@link SimpleGMF.Model#getClasses <em>Classes</em>}</li>
 * </ul>
 * </p>
 *
 * @see SimpleGMF.SimpleGMFPackage#getModel()
 * @model
 * @generated
 */
public interface Model extends EObject {
	/**
	 * Returns the value of the '<em><b>Classes</b></em>' containment reference list.
	 * The list contents are of type {@link SimpleGMF.SimpleClass}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Classes</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Classes</em>' containment reference list.
	 * @see SimpleGMF.SimpleGMFPackage#getModel_Classes()
	 * @model containment="true"
	 * @generated
	 */
	EList<SimpleClass> getClasses();

} // Model

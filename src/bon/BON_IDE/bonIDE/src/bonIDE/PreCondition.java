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
 * A representation of the model object '<em><b>Pre Condition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.PreCondition#getContent <em>Content</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getPreCondition()
 * @model
 * @generated
 */
public interface PreCondition extends EObject {
	/**
	 * Returns the value of the '<em><b>Content</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Content</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Content</em>' attribute.
	 * @see #setContent(String)
	 * @see bonIDE.BonIDEPackage#getPreCondition_Content()
	 * @model
	 * @generated
	 */
	String getContent();

	/**
	 * Sets the value of the '{@link bonIDE.PreCondition#getContent <em>Content</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Content</em>' attribute.
	 * @see #getContent()
	 * @generated
	 */
	void setContent(String value);

} // PreCondition

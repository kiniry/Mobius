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
 * A representation of the model object '<em><b>Index Clause</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.IndexClause#getIdentifier <em>Identifier</em>}</li>
 *   <li>{@link bonIDE.IndexClause#getTerms <em>Terms</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getIndexClause()
 * @model
 * @generated
 */
public interface IndexClause extends EObject {
	/**
	 * Returns the value of the '<em><b>Identifier</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Identifier</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Identifier</em>' attribute.
	 * @see #setIdentifier(String)
	 * @see bonIDE.BonIDEPackage#getIndexClause_Identifier()
	 * @model
	 * @generated
	 */
	String getIdentifier();

	/**
	 * Sets the value of the '{@link bonIDE.IndexClause#getIdentifier <em>Identifier</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Identifier</em>' attribute.
	 * @see #getIdentifier()
	 * @generated
	 */
	void setIdentifier(String value);

	/**
	 * Returns the value of the '<em><b>Terms</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.String}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Terms</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Terms</em>' attribute list.
	 * @see bonIDE.BonIDEPackage#getIndexClause_Terms()
	 * @model
	 * @generated
	 */
	EList<String> getTerms();

} // IndexClause

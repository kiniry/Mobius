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
 * A representation of the model object '<em><b>Inheritance Clause</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.InheritanceClause#getParentNames <em>Parent Names</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getInheritanceClause()
 * @model
 * @generated
 */
public interface InheritanceClause extends EObject {
	/**
	 * Returns the value of the '<em><b>Parent Names</b></em>' attribute list.
	 * The list contents are of type {@link java.lang.String}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Parent Names</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parent Names</em>' attribute list.
	 * @see bonIDE.BonIDEPackage#getInheritanceClause_ParentNames()
	 * @model
	 * @generated
	 */
	EList<String> getParentNames();

} // InheritanceClause

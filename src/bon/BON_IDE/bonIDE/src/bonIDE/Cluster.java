/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Cluster</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.Cluster#getContents <em>Contents</em>}</li>
 *   <li>{@link bonIDE.Cluster#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.Cluster#isCollapsed <em>Collapsed</em>}</li>
 *   <li>{@link bonIDE.Cluster#getExpandedHeight <em>Expanded Height</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getCluster()
 * @model
 * @generated
 */
public interface Cluster extends StaticAbstraction {
	/**
	 * Returns the value of the '<em><b>Contents</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.StaticAbstraction}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Contents</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Contents</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getCluster_Contents()
	 * @model containment="true"
	 * @generated
	 */
	EList<StaticAbstraction> getContents();

	/**
	 * Returns the value of the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Name</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Name</em>' attribute.
	 * @see #setName(String)
	 * @see bonIDE.BonIDEPackage#getCluster_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link bonIDE.Cluster#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

	/**
	 * Returns the value of the '<em><b>Collapsed</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Collapsed</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Collapsed</em>' attribute.
	 * @see #setCollapsed(boolean)
	 * @see bonIDE.BonIDEPackage#getCluster_Collapsed()
	 * @model
	 * @generated
	 */
	boolean isCollapsed();

	/**
	 * Sets the value of the '{@link bonIDE.Cluster#isCollapsed <em>Collapsed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Collapsed</em>' attribute.
	 * @see #isCollapsed()
	 * @generated
	 */
	void setCollapsed(boolean value);

	/**
	 * Returns the value of the '<em><b>Expanded Height</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Expanded Height</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Expanded Height</em>' attribute.
	 * @see #setExpandedHeight(int)
	 * @see bonIDE.BonIDEPackage#getCluster_ExpandedHeight()
	 * @model
	 * @generated
	 */
	int getExpandedHeight();

	/**
	 * Sets the value of the '{@link bonIDE.Cluster#getExpandedHeight <em>Expanded Height</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Expanded Height</em>' attribute.
	 * @see #getExpandedHeight()
	 * @generated
	 */
	void setExpandedHeight(int value);

} // Cluster

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Cluster</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link BONModel.Cluster#getContents <em>Contents</em>}</li>
 * </ul>
 * </p>
 *
 * @see BONModel.BONModelPackage#getCluster()
 * @model
 * @generated
 */
public interface Cluster extends StaticAbstraction {
	/**
	 * Returns the value of the '<em><b>Contents</b></em>' reference list.
	 * The list contents are of type {@link BONModel.StaticAbstraction}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Contents</em>' reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Contents</em>' reference list.
	 * @see BONModel.BONModelPackage#getCluster_Contents()
	 * @model
	 * @generated
	 */
	EList<StaticAbstraction> getContents();

} // Cluster

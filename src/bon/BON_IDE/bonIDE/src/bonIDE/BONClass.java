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
 * A representation of the model object '<em><b>BON Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link bonIDE.BONClass#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.BONClass#getFeatures <em>Features</em>}</li>
 *   <li>{@link bonIDE.BONClass#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link bonIDE.BONClass#getImplementationStatus <em>Implementation Status</em>}</li>
 *   <li>{@link bonIDE.BONClass#getIndexes <em>Indexes</em>}</li>
 *   <li>{@link bonIDE.BONClass#getParents <em>Parents</em>}</li>
 *   <li>{@link bonIDE.BONClass#getInvariants <em>Invariants</em>}</li>
 * </ul>
 * </p>
 *
 * @see bonIDE.BonIDEPackage#getBONClass()
 * @model
 * @generated
 */
public interface BONClass extends StaticAbstraction {
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
	 * @see bonIDE.BonIDEPackage#getBONClass_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

	/**
	 * Returns the value of the '<em><b>Features</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.Feature}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Features</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Features</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getBONClass_Features()
	 * @model containment="true"
	 * @generated
	 */
	EList<Feature> getFeatures();

	/**
	 * Returns the value of the '<em><b>Is Deferred</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Is Deferred</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Is Deferred</em>' attribute.
	 * @see #setIsDeferred(boolean)
	 * @see bonIDE.BonIDEPackage#getBONClass_IsDeferred()
	 * @model
	 * @generated
	 */
	boolean isIsDeferred();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#isIsDeferred <em>Is Deferred</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Is Deferred</em>' attribute.
	 * @see #isIsDeferred()
	 * @generated
	 */
	void setIsDeferred(boolean value);

	/**
	 * Returns the value of the '<em><b>Parents</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Parents</em>' attribute list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parents</em>' containment reference.
	 * @see #setParents(InheritanceClause)
	 * @see bonIDE.BonIDEPackage#getBONClass_Parents()
	 * @model containment="true"
	 * @generated
	 */
	InheritanceClause getParents();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#getParents <em>Parents</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Parents</em>' containment reference.
	 * @see #getParents()
	 * @generated
	 */
	void setParents(InheritanceClause value);

	/**
	 * Returns the value of the '<em><b>Invariants</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.Invariant}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Invariants</em>' containment reference list isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Invariants</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getBONClass_Invariants()
	 * @model containment="true"
	 * @generated
	 */
	EList<Invariant> getInvariants();

	/**
	 * Returns the value of the '<em><b>Indexes</b></em>' containment reference list.
	 * The list contents are of type {@link bonIDE.IndexClause}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Indexes</em>' containment reference isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Indexes</em>' containment reference list.
	 * @see bonIDE.BonIDEPackage#getBONClass_Indexes()
	 * @model containment="true"
	 * @generated
	 */
	EList<IndexClause> getIndexes();

	/**
	 * Returns the value of the '<em><b>Implementation Status</b></em>' attribute.
	 * The default value is <code>"Effective"</code>.
	 * The literals are from the enumeration {@link bonIDE.ImplementationStatus}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Implementation Status</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Implementation Status</em>' attribute.
	 * @see bonIDE.ImplementationStatus
	 * @see #setImplementationStatus(ImplementationStatus)
	 * @see bonIDE.BonIDEPackage#getBONClass_ImplementationStatus()
	 * @model default="Effective"
	 * @generated
	 */
	ImplementationStatus getImplementationStatus();

	/**
	 * Sets the value of the '{@link bonIDE.BONClass#getImplementationStatus <em>Implementation Status</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Implementation Status</em>' attribute.
	 * @see bonIDE.ImplementationStatus
	 * @see #getImplementationStatus()
	 * @generated
	 */
	void setImplementationStatus(ImplementationStatus value);

} // BONClass

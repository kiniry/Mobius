/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.impl;

import bonIDE.BonIDEPackage;
import bonIDE.InheritanceClause;

import java.util.Collection;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Inheritance Clause</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link bonIDE.impl.InheritanceClauseImpl#getParentNames <em>Parent Names</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class InheritanceClauseImpl extends EObjectImpl implements InheritanceClause {
	/**
	 * The cached value of the '{@link #getParentNames() <em>Parent Names</em>}' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getParentNames()
	 * @generated
	 * @ordered
	 */
	protected EList<String> parentNames;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected InheritanceClauseImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BonIDEPackage.Literals.INHERITANCE_CLAUSE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<String> getParentNames() {
		if (parentNames == null) {
			parentNames = new EDataTypeUniqueEList<String>(String.class, this, BonIDEPackage.INHERITANCE_CLAUSE__PARENT_NAMES);
		}
		return parentNames;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BonIDEPackage.INHERITANCE_CLAUSE__PARENT_NAMES:
				return getParentNames();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
			case BonIDEPackage.INHERITANCE_CLAUSE__PARENT_NAMES:
				getParentNames().clear();
				getParentNames().addAll((Collection<? extends String>)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID) {
		switch (featureID) {
			case BonIDEPackage.INHERITANCE_CLAUSE__PARENT_NAMES:
				getParentNames().clear();
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID) {
		switch (featureID) {
			case BonIDEPackage.INHERITANCE_CLAUSE__PARENT_NAMES:
				return parentNames != null && !parentNames.isEmpty();
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString() {
		if (eIsProxy()) return super.toString();

		StringBuffer result = new StringBuffer(super.toString());
		result.append(" (parentNames: ");
		result.append(parentNames);
		result.append(')');
		return result.toString();
	}

} //InheritanceClauseImpl

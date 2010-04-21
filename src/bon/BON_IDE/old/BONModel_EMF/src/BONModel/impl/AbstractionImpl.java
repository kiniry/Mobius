/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.Abstraction;
import BONModel.BONModelPackage;
import BONModel.Relationship;

import java.util.Collection;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstraction</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link BONModel.impl.AbstractionImpl#getRelationships <em>Relationships</em>}</li>
 *   <li>{@link BONModel.impl.AbstractionImpl#getContains <em>Contains</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractionImpl extends EObjectImpl implements Abstraction {
	/**
	 * The cached value of the '{@link #getRelationships() <em>Relationships</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRelationships()
	 * @generated
	 * @ordered
	 */
	protected EList<Relationship> relationships;

	/**
	 * The cached value of the '{@link #getContains() <em>Contains</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getContains()
	 * @generated
	 * @ordered
	 */
	protected EList<Abstraction> contains;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected AbstractionImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BONModelPackage.Literals.ABSTRACTION;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Relationship> getRelationships() {
		if (relationships == null) {
			relationships = new EObjectResolvingEList<Relationship>(Relationship.class, this, BONModelPackage.ABSTRACTION__RELATIONSHIPS);
		}
		return relationships;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Abstraction> getContains() {
		if (contains == null) {
			contains = new EObjectResolvingEList<Abstraction>(Abstraction.class, this, BONModelPackage.ABSTRACTION__CONTAINS);
		}
		return contains;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BONModelPackage.ABSTRACTION__RELATIONSHIPS:
				return getRelationships();
			case BONModelPackage.ABSTRACTION__CONTAINS:
				return getContains();
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
			case BONModelPackage.ABSTRACTION__RELATIONSHIPS:
				getRelationships().clear();
				getRelationships().addAll((Collection<? extends Relationship>)newValue);
				return;
			case BONModelPackage.ABSTRACTION__CONTAINS:
				getContains().clear();
				getContains().addAll((Collection<? extends Abstraction>)newValue);
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
			case BONModelPackage.ABSTRACTION__RELATIONSHIPS:
				getRelationships().clear();
				return;
			case BONModelPackage.ABSTRACTION__CONTAINS:
				getContains().clear();
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
			case BONModelPackage.ABSTRACTION__RELATIONSHIPS:
				return relationships != null && !relationships.isEmpty();
			case BONModelPackage.ABSTRACTION__CONTAINS:
				return contains != null && !contains.isEmpty();
		}
		return super.eIsSet(featureID);
	}

} //AbstractionImpl

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.Abstraction;
import BONModel.BONModelPackage;
import BONModel.Feature;
import BONModel.Inheritance;
import BONModel.Model;
import BONModel.Relationship;

import java.util.Collection;

import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Model</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link BONModel.impl.ModelImpl#getClosure <em>Closure</em>}</li>
 *   <li>{@link BONModel.impl.ModelImpl#getAbstractions <em>Abstractions</em>}</li>
 *   <li>{@link BONModel.impl.ModelImpl#getRelationships <em>Relationships</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ModelImpl extends EObjectImpl implements Model {
	/**
	 * The cached value of the '{@link #getClosure() <em>Closure</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getClosure()
	 * @generated
	 * @ordered
	 */
	protected EList<Inheritance> closure;

	/**
	 * The cached value of the '{@link #getAbstractions() <em>Abstractions</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAbstractions()
	 * @generated
	 * @ordered
	 */
	protected EList<Abstraction> abstractions;

	/**
	 * The cached value of the '{@link #getRelationships() <em>Relationships</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRelationships()
	 * @generated
	 * @ordered
	 */
	protected EList<Relationship> relationships;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ModelImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BONModelPackage.Literals.MODEL;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Relationship> getRelationships() {
		if (relationships == null) {
			relationships = new EObjectContainmentEList<Relationship>(Relationship.class, this, BONModelPackage.MODEL__RELATIONSHIPS);
		}
		return relationships;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Inheritance> getClosure() {
		if (closure == null) {
			closure = new EObjectResolvingEList<Inheritance>(Inheritance.class, this, BONModelPackage.MODEL__CLOSURE);
		}
		return closure;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Abstraction> getAbstractions() {
		if (abstractions == null) {
			abstractions = new EObjectContainmentEList<Abstraction>(Abstraction.class, this, BONModelPackage.MODEL__ABSTRACTIONS);
		}
		return abstractions;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Boolean covariant(Feature featureOne, Feature featureTwo) {
		// TODO: implement this method
		// Ensure that you remove @generated or mark it @generated NOT
		throw new UnsupportedOperationException();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
		switch (featureID) {
			case BONModelPackage.MODEL__ABSTRACTIONS:
				return ((InternalEList<?>)getAbstractions()).basicRemove(otherEnd, msgs);
			case BONModelPackage.MODEL__RELATIONSHIPS:
				return ((InternalEList<?>)getRelationships()).basicRemove(otherEnd, msgs);
		}
		return super.eInverseRemove(otherEnd, featureID, msgs);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BONModelPackage.MODEL__CLOSURE:
				return getClosure();
			case BONModelPackage.MODEL__ABSTRACTIONS:
				return getAbstractions();
			case BONModelPackage.MODEL__RELATIONSHIPS:
				return getRelationships();
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
			case BONModelPackage.MODEL__CLOSURE:
				getClosure().clear();
				getClosure().addAll((Collection<? extends Inheritance>)newValue);
				return;
			case BONModelPackage.MODEL__ABSTRACTIONS:
				getAbstractions().clear();
				getAbstractions().addAll((Collection<? extends Abstraction>)newValue);
				return;
			case BONModelPackage.MODEL__RELATIONSHIPS:
				getRelationships().clear();
				getRelationships().addAll((Collection<? extends Relationship>)newValue);
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
			case BONModelPackage.MODEL__CLOSURE:
				getClosure().clear();
				return;
			case BONModelPackage.MODEL__ABSTRACTIONS:
				getAbstractions().clear();
				return;
			case BONModelPackage.MODEL__RELATIONSHIPS:
				getRelationships().clear();
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
			case BONModelPackage.MODEL__CLOSURE:
				return closure != null && !closure.isEmpty();
			case BONModelPackage.MODEL__ABSTRACTIONS:
				return abstractions != null && !abstractions.isEmpty();
			case BONModelPackage.MODEL__RELATIONSHIPS:
				return relationships != null && !relationships.isEmpty();
		}
		return super.eIsSet(featureID);
	}

} //ModelImpl

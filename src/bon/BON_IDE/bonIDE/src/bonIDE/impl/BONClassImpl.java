/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.impl;

import bonIDE.BONClass;
import bonIDE.BonIDEPackage;
import bonIDE.Feature;

import bonIDE.ImplementationStatus;
import bonIDE.IndexClause;
import bonIDE.InheritanceClause;
import bonIDE.Invariant;
import bonIDE.Parent;
import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>BON Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link bonIDE.impl.BONClassImpl#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#getFeatures <em>Features</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#getImplementationStatus <em>Implementation Status</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#getIndexes <em>Indexes</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#getParents <em>Parents</em>}</li>
 *   <li>{@link bonIDE.impl.BONClassImpl#getInvariants <em>Invariants</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class BONClassImpl extends StaticAbstractionImpl implements BONClass {
	/**
	 * The default value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected static final String NAME_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected String name = NAME_EDEFAULT;

	/**
	 * The cached value of the '{@link #getFeatures() <em>Features</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getFeatures()
	 * @generated
	 * @ordered
	 */
	protected EList<Feature> features;

	/**
	 * The default value of the '{@link #isIsDeferred() <em>Is Deferred</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsDeferred()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_DEFERRED_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsDeferred() <em>Is Deferred</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsDeferred()
	 * @generated
	 * @ordered
	 */
	protected boolean isDeferred = IS_DEFERRED_EDEFAULT;

	/**
	 * The default value of the '{@link #getImplementationStatus() <em>Implementation Status</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getImplementationStatus()
	 * @generated
	 * @ordered
	 */
	protected static final ImplementationStatus IMPLEMENTATION_STATUS_EDEFAULT = ImplementationStatus.EFFECTIVE;

	/**
	 * The cached value of the '{@link #getImplementationStatus() <em>Implementation Status</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getImplementationStatus()
	 * @generated
	 * @ordered
	 */
	protected ImplementationStatus implementationStatus = IMPLEMENTATION_STATUS_EDEFAULT;

	/**
	 * The cached value of the '{@link #getIndexes() <em>Indexes</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getIndexes()
	 * @generated
	 * @ordered
	 */
	protected EList<IndexClause> indexes;

	/**
	 * The cached value of the '{@link #getParents() <em>Parents</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getParents()
	 * @generated
	 * @ordered
	 */
	protected InheritanceClause parents;

	/**
	 * The cached value of the '{@link #getInvariants() <em>Invariants</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getInvariants()
	 * @generated
	 * @ordered
	 */
	protected EList<Invariant> invariants;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected BONClassImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BonIDEPackage.Literals.BON_CLASS;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getName() {
		return name;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setName(String newName) {
		String oldName = name;
		name = newName;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.BON_CLASS__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Feature> getFeatures() {
		if (features == null) {
			features = new EObjectContainmentEList<Feature>(Feature.class, this, BonIDEPackage.BON_CLASS__FEATURES);
		}
		return features;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsDeferred() {
		return isDeferred;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsDeferred(boolean newIsDeferred) {
		boolean oldIsDeferred = isDeferred;
		isDeferred = newIsDeferred;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.BON_CLASS__IS_DEFERRED, oldIsDeferred, isDeferred));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InheritanceClause getParents() {
		return parents;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetParents(InheritanceClause newParents, NotificationChain msgs) {
		InheritanceClause oldParents = parents;
		parents = newParents;
		if (eNotificationRequired()) {
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, BonIDEPackage.BON_CLASS__PARENTS, oldParents, newParents);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setParents(InheritanceClause newParents) {
		if (newParents != parents) {
			NotificationChain msgs = null;
			if (parents != null)
				msgs = ((InternalEObject)parents).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - BonIDEPackage.BON_CLASS__PARENTS, null, msgs);
			if (newParents != null)
				msgs = ((InternalEObject)newParents).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - BonIDEPackage.BON_CLASS__PARENTS, null, msgs);
			msgs = basicSetParents(newParents, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.BON_CLASS__PARENTS, newParents, newParents));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Invariant> getInvariants() {
		if (invariants == null) {
			invariants = new EObjectContainmentEList<Invariant>(Invariant.class, this, BonIDEPackage.BON_CLASS__INVARIANTS);
		}
		return invariants;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<IndexClause> getIndexes() {
		if (indexes == null) {
			indexes = new EObjectContainmentEList<IndexClause>(IndexClause.class, this, BonIDEPackage.BON_CLASS__INDEXES);
		}
		return indexes;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ImplementationStatus getImplementationStatus() {
		return implementationStatus;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setImplementationStatus(ImplementationStatus newImplementationStatus) {
		ImplementationStatus oldImplementationStatus = implementationStatus;
		implementationStatus = newImplementationStatus == null ? IMPLEMENTATION_STATUS_EDEFAULT : newImplementationStatus;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.BON_CLASS__IMPLEMENTATION_STATUS, oldImplementationStatus, implementationStatus));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
		switch (featureID) {
			case BonIDEPackage.BON_CLASS__FEATURES:
				return ((InternalEList<?>)getFeatures()).basicRemove(otherEnd, msgs);
			case BonIDEPackage.BON_CLASS__INDEXES:
				return ((InternalEList<?>)getIndexes()).basicRemove(otherEnd, msgs);
			case BonIDEPackage.BON_CLASS__PARENTS:
				return basicSetParents(null, msgs);
			case BonIDEPackage.BON_CLASS__INVARIANTS:
				return ((InternalEList<?>)getInvariants()).basicRemove(otherEnd, msgs);
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
			case BonIDEPackage.BON_CLASS__NAME:
				return getName();
			case BonIDEPackage.BON_CLASS__FEATURES:
				return getFeatures();
			case BonIDEPackage.BON_CLASS__IS_DEFERRED:
				return isIsDeferred();
			case BonIDEPackage.BON_CLASS__IMPLEMENTATION_STATUS:
				return getImplementationStatus();
			case BonIDEPackage.BON_CLASS__INDEXES:
				return getIndexes();
			case BonIDEPackage.BON_CLASS__PARENTS:
				return getParents();
			case BonIDEPackage.BON_CLASS__INVARIANTS:
				return getInvariants();
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
			case BonIDEPackage.BON_CLASS__NAME:
				setName((String)newValue);
				return;
			case BonIDEPackage.BON_CLASS__FEATURES:
				getFeatures().clear();
				getFeatures().addAll((Collection<? extends Feature>)newValue);
				return;
			case BonIDEPackage.BON_CLASS__IS_DEFERRED:
				setIsDeferred((Boolean)newValue);
				return;
			case BonIDEPackage.BON_CLASS__IMPLEMENTATION_STATUS:
				setImplementationStatus((ImplementationStatus)newValue);
				return;
			case BonIDEPackage.BON_CLASS__INDEXES:
				getIndexes().clear();
				getIndexes().addAll((Collection<? extends IndexClause>)newValue);
				return;
			case BonIDEPackage.BON_CLASS__PARENTS:
				setParents((InheritanceClause)newValue);
				return;
			case BonIDEPackage.BON_CLASS__INVARIANTS:
				getInvariants().clear();
				getInvariants().addAll((Collection<? extends Invariant>)newValue);
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
			case BonIDEPackage.BON_CLASS__NAME:
				setName(NAME_EDEFAULT);
				return;
			case BonIDEPackage.BON_CLASS__FEATURES:
				getFeatures().clear();
				return;
			case BonIDEPackage.BON_CLASS__IS_DEFERRED:
				setIsDeferred(IS_DEFERRED_EDEFAULT);
				return;
			case BonIDEPackage.BON_CLASS__IMPLEMENTATION_STATUS:
				setImplementationStatus(IMPLEMENTATION_STATUS_EDEFAULT);
				return;
			case BonIDEPackage.BON_CLASS__INDEXES:
				getIndexes().clear();
				return;
			case BonIDEPackage.BON_CLASS__PARENTS:
				setParents((InheritanceClause)null);
				return;
			case BonIDEPackage.BON_CLASS__INVARIANTS:
				getInvariants().clear();
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
			case BonIDEPackage.BON_CLASS__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case BonIDEPackage.BON_CLASS__FEATURES:
				return features != null && !features.isEmpty();
			case BonIDEPackage.BON_CLASS__IS_DEFERRED:
				return isDeferred != IS_DEFERRED_EDEFAULT;
			case BonIDEPackage.BON_CLASS__IMPLEMENTATION_STATUS:
				return implementationStatus != IMPLEMENTATION_STATUS_EDEFAULT;
			case BonIDEPackage.BON_CLASS__INDEXES:
				return indexes != null && !indexes.isEmpty();
			case BonIDEPackage.BON_CLASS__PARENTS:
				return parents != null;
			case BonIDEPackage.BON_CLASS__INVARIANTS:
				return invariants != null && !invariants.isEmpty();
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
		result.append(" (name: ");
		result.append(name);
		result.append(", isDeferred: ");
		result.append(isDeferred);
		result.append(", implementationStatus: ");
		result.append(implementationStatus);
		result.append(')');
		return result.toString();
	}

} //BONClassImpl

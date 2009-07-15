/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.BONModelPackage;
import BONModel.Call;
import BONModel.Feature;
import BONModel.Renaming;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link BONModel.impl.ClassImpl#getCallsInInvariants <em>Calls In Invariants</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getFeatures <em>Features</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getClientFeatures <em>Client Features</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getRenamings <em>Renamings</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getRenameClassParents <em>Rename Class Parents</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#isIsEffective <em>Is Effective</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#isIsPersistent <em>Is Persistent</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#isIsExternal <em>Is External</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#isIsRoot <em>Is Root</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getRedefined <em>Redefined</em>}</li>
 *   <li>{@link BONModel.impl.ClassImpl#getAllNames <em>All Names</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ClassImpl extends StaticAbstractionImpl implements BONModel.Class {
	/**
	 * The cached value of the '{@link #getCallsInInvariants() <em>Calls In Invariants</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCallsInInvariants()
	 * @generated
	 * @ordered
	 */
	protected EList<Call> callsInInvariants;

	/**
	 * The cached value of the '{@link #getFeatures() <em>Features</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getFeatures()
	 * @generated
	 * @ordered
	 */
	protected EList<Feature> features;

	/**
	 * The cached value of the '{@link #getClientFeatures() <em>Client Features</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getClientFeatures()
	 * @generated
	 * @ordered
	 */
	protected EList<Feature> clientFeatures;

	/**
	 * The cached value of the '{@link #getRenamings() <em>Renamings</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRenamings()
	 * @generated
	 * @ordered
	 */
	protected EList<Renaming> renamings;

	/**
	 * The cached value of the '{@link #getRenameClassParents() <em>Rename Class Parents</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRenameClassParents()
	 * @generated
	 * @ordered
	 */
	protected EList<BONModel.Class> renameClassParents;

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
	 * The default value of the '{@link #isIsEffective() <em>Is Effective</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsEffective()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_EFFECTIVE_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsEffective() <em>Is Effective</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsEffective()
	 * @generated
	 * @ordered
	 */
	protected boolean isEffective = IS_EFFECTIVE_EDEFAULT;

	/**
	 * The default value of the '{@link #isIsPersistent() <em>Is Persistent</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsPersistent()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_PERSISTENT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsPersistent() <em>Is Persistent</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsPersistent()
	 * @generated
	 * @ordered
	 */
	protected boolean isPersistent = IS_PERSISTENT_EDEFAULT;

	/**
	 * The default value of the '{@link #isIsExternal() <em>Is External</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsExternal()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_EXTERNAL_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsExternal() <em>Is External</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsExternal()
	 * @generated
	 * @ordered
	 */
	protected boolean isExternal = IS_EXTERNAL_EDEFAULT;

	/**
	 * The default value of the '{@link #isIsRoot() <em>Is Root</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsRoot()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_ROOT_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsRoot() <em>Is Root</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsRoot()
	 * @generated
	 * @ordered
	 */
	protected boolean isRoot = IS_ROOT_EDEFAULT;

	/**
	 * The cached value of the '{@link #getRedefined() <em>Redefined</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getRedefined()
	 * @generated
	 * @ordered
	 */
	protected EList<Feature> redefined;

	/**
	 * The cached value of the '{@link #getAllNames() <em>All Names</em>}' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAllNames()
	 * @generated
	 * @ordered
	 */
	protected EList<String> allNames;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ClassImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BONModelPackage.Literals.CLASS;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Call> getCallsInInvariants() {
		if (callsInInvariants == null) {
			callsInInvariants = new EObjectResolvingEList<Call>(Call.class, this, BONModelPackage.CLASS__CALLS_IN_INVARIANTS);
		}
		return callsInInvariants;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Feature> getFeatures() {
		if (features == null) {
			features = new EObjectResolvingEList<Feature>(Feature.class, this, BONModelPackage.CLASS__FEATURES);
		}
		return features;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Feature> getClientFeatures() {
		if (clientFeatures == null) {
			clientFeatures = new EObjectResolvingEList<Feature>(Feature.class, this, BONModelPackage.CLASS__CLIENT_FEATURES);
		}
		return clientFeatures;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Renaming> getRenamings() {
		if (renamings == null) {
			renamings = new EObjectResolvingEList<Renaming>(Renaming.class, this, BONModelPackage.CLASS__RENAMINGS);
		}
		return renamings;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<BONModel.Class> getRenameClassParents() {
		if (renameClassParents == null) {
			renameClassParents = new EObjectResolvingEList<BONModel.Class>(BONModel.Class.class, this, BONModelPackage.CLASS__RENAME_CLASS_PARENTS);
		}
		return renameClassParents;
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
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CLASS__IS_DEFERRED, oldIsDeferred, isDeferred));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsEffective() {
		return isEffective;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsEffective(boolean newIsEffective) {
		boolean oldIsEffective = isEffective;
		isEffective = newIsEffective;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CLASS__IS_EFFECTIVE, oldIsEffective, isEffective));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsPersistent() {
		return isPersistent;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsPersistent(boolean newIsPersistent) {
		boolean oldIsPersistent = isPersistent;
		isPersistent = newIsPersistent;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CLASS__IS_PERSISTENT, oldIsPersistent, isPersistent));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsExternal() {
		return isExternal;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsExternal(boolean newIsExternal) {
		boolean oldIsExternal = isExternal;
		isExternal = newIsExternal;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CLASS__IS_EXTERNAL, oldIsExternal, isExternal));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsRoot() {
		return isRoot;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsRoot(boolean newIsRoot) {
		boolean oldIsRoot = isRoot;
		isRoot = newIsRoot;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CLASS__IS_ROOT, oldIsRoot, isRoot));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Feature> getRedefined() {
		if (redefined == null) {
			redefined = new EObjectResolvingEList<Feature>(Feature.class, this, BONModelPackage.CLASS__REDEFINED);
		}
		return redefined;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<String> getAllNames() {
		if (allNames == null) {
			allNames = new EDataTypeUniqueEList<String>(String.class, this, BONModelPackage.CLASS__ALL_NAMES);
		}
		return allNames;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BONModelPackage.CLASS__CALLS_IN_INVARIANTS:
				return getCallsInInvariants();
			case BONModelPackage.CLASS__FEATURES:
				return getFeatures();
			case BONModelPackage.CLASS__CLIENT_FEATURES:
				return getClientFeatures();
			case BONModelPackage.CLASS__RENAMINGS:
				return getRenamings();
			case BONModelPackage.CLASS__RENAME_CLASS_PARENTS:
				return getRenameClassParents();
			case BONModelPackage.CLASS__IS_DEFERRED:
				return isIsDeferred() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.CLASS__IS_EFFECTIVE:
				return isIsEffective() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.CLASS__IS_PERSISTENT:
				return isIsPersistent() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.CLASS__IS_EXTERNAL:
				return isIsExternal() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.CLASS__IS_ROOT:
				return isIsRoot() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.CLASS__REDEFINED:
				return getRedefined();
			case BONModelPackage.CLASS__ALL_NAMES:
				return getAllNames();
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
			case BONModelPackage.CLASS__CALLS_IN_INVARIANTS:
				getCallsInInvariants().clear();
				getCallsInInvariants().addAll((Collection<? extends Call>)newValue);
				return;
			case BONModelPackage.CLASS__FEATURES:
				getFeatures().clear();
				getFeatures().addAll((Collection<? extends Feature>)newValue);
				return;
			case BONModelPackage.CLASS__CLIENT_FEATURES:
				getClientFeatures().clear();
				getClientFeatures().addAll((Collection<? extends Feature>)newValue);
				return;
			case BONModelPackage.CLASS__RENAMINGS:
				getRenamings().clear();
				getRenamings().addAll((Collection<? extends Renaming>)newValue);
				return;
			case BONModelPackage.CLASS__RENAME_CLASS_PARENTS:
				getRenameClassParents().clear();
				getRenameClassParents().addAll((Collection<? extends BONModel.Class>)newValue);
				return;
			case BONModelPackage.CLASS__IS_DEFERRED:
				setIsDeferred(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.CLASS__IS_EFFECTIVE:
				setIsEffective(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.CLASS__IS_PERSISTENT:
				setIsPersistent(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.CLASS__IS_EXTERNAL:
				setIsExternal(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.CLASS__IS_ROOT:
				setIsRoot(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.CLASS__REDEFINED:
				getRedefined().clear();
				getRedefined().addAll((Collection<? extends Feature>)newValue);
				return;
			case BONModelPackage.CLASS__ALL_NAMES:
				getAllNames().clear();
				getAllNames().addAll((Collection<? extends String>)newValue);
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
			case BONModelPackage.CLASS__CALLS_IN_INVARIANTS:
				getCallsInInvariants().clear();
				return;
			case BONModelPackage.CLASS__FEATURES:
				getFeatures().clear();
				return;
			case BONModelPackage.CLASS__CLIENT_FEATURES:
				getClientFeatures().clear();
				return;
			case BONModelPackage.CLASS__RENAMINGS:
				getRenamings().clear();
				return;
			case BONModelPackage.CLASS__RENAME_CLASS_PARENTS:
				getRenameClassParents().clear();
				return;
			case BONModelPackage.CLASS__IS_DEFERRED:
				setIsDeferred(IS_DEFERRED_EDEFAULT);
				return;
			case BONModelPackage.CLASS__IS_EFFECTIVE:
				setIsEffective(IS_EFFECTIVE_EDEFAULT);
				return;
			case BONModelPackage.CLASS__IS_PERSISTENT:
				setIsPersistent(IS_PERSISTENT_EDEFAULT);
				return;
			case BONModelPackage.CLASS__IS_EXTERNAL:
				setIsExternal(IS_EXTERNAL_EDEFAULT);
				return;
			case BONModelPackage.CLASS__IS_ROOT:
				setIsRoot(IS_ROOT_EDEFAULT);
				return;
			case BONModelPackage.CLASS__REDEFINED:
				getRedefined().clear();
				return;
			case BONModelPackage.CLASS__ALL_NAMES:
				getAllNames().clear();
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
			case BONModelPackage.CLASS__CALLS_IN_INVARIANTS:
				return callsInInvariants != null && !callsInInvariants.isEmpty();
			case BONModelPackage.CLASS__FEATURES:
				return features != null && !features.isEmpty();
			case BONModelPackage.CLASS__CLIENT_FEATURES:
				return clientFeatures != null && !clientFeatures.isEmpty();
			case BONModelPackage.CLASS__RENAMINGS:
				return renamings != null && !renamings.isEmpty();
			case BONModelPackage.CLASS__RENAME_CLASS_PARENTS:
				return renameClassParents != null && !renameClassParents.isEmpty();
			case BONModelPackage.CLASS__IS_DEFERRED:
				return isDeferred != IS_DEFERRED_EDEFAULT;
			case BONModelPackage.CLASS__IS_EFFECTIVE:
				return isEffective != IS_EFFECTIVE_EDEFAULT;
			case BONModelPackage.CLASS__IS_PERSISTENT:
				return isPersistent != IS_PERSISTENT_EDEFAULT;
			case BONModelPackage.CLASS__IS_EXTERNAL:
				return isExternal != IS_EXTERNAL_EDEFAULT;
			case BONModelPackage.CLASS__IS_ROOT:
				return isRoot != IS_ROOT_EDEFAULT;
			case BONModelPackage.CLASS__REDEFINED:
				return redefined != null && !redefined.isEmpty();
			case BONModelPackage.CLASS__ALL_NAMES:
				return allNames != null && !allNames.isEmpty();
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
		result.append(" (isDeferred: ");
		result.append(isDeferred);
		result.append(", isEffective: ");
		result.append(isEffective);
		result.append(", isPersistent: ");
		result.append(isPersistent);
		result.append(", isExternal: ");
		result.append(isExternal);
		result.append(", isRoot: ");
		result.append(isRoot);
		result.append(", allNames: ");
		result.append(allNames);
		result.append(')');
		return result.toString();
	}

} //ClassImpl

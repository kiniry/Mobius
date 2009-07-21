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
import BONModel.Parameter;
import BONModel.Query;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Feature</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link BONModel.impl.FeatureImpl#isIsDeferred <em>Is Deferred</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#isIsEffective <em>Is Effective</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#isIsRedefined <em>Is Redefined</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getName <em>Name</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getAccessors <em>Accessors</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getCallsInPrecondition <em>Calls In Precondition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getCallsInPostcondition <em>Calls In Postcondition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getFrame <em>Frame</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class FeatureImpl extends EObjectImpl implements Feature {
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
	 * The default value of the '{@link #isIsRedefined() <em>Is Redefined</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsRedefined()
	 * @generated
	 * @ordered
	 */
	protected static final boolean IS_REDEFINED_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isIsRedefined() <em>Is Redefined</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isIsRedefined()
	 * @generated
	 * @ordered
	 */
	protected boolean isRedefined = IS_REDEFINED_EDEFAULT;

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
	 * The cached value of the '{@link #getAccessors() <em>Accessors</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getAccessors()
	 * @generated
	 * @ordered
	 */
	protected EList<BONModel.Class> accessors;

	/**
	 * The cached value of the '{@link #getParameters() <em>Parameters</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getParameters()
	 * @generated
	 * @ordered
	 */
	protected EList<Parameter> parameters;

	/**
	 * The cached value of the '{@link #getCallsInPrecondition() <em>Calls In Precondition</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCallsInPrecondition()
	 * @generated
	 * @ordered
	 */
	protected EList<Call> callsInPrecondition;

	/**
	 * The cached value of the '{@link #getCallsInPostcondition() <em>Calls In Postcondition</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getCallsInPostcondition()
	 * @generated
	 * @ordered
	 */
	protected EList<Call> callsInPostcondition;

	/**
	 * The cached value of the '{@link #getFrame() <em>Frame</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getFrame()
	 * @generated
	 * @ordered
	 */
	protected EList<Query> frame;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected FeatureImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BONModelPackage.Literals.FEATURE;
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
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__IS_DEFERRED, oldIsDeferred, isDeferred));
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
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__IS_EFFECTIVE, oldIsEffective, isEffective));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isIsRedefined() {
		return isRedefined;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setIsRedefined(boolean newIsRedefined) {
		boolean oldIsRedefined = isRedefined;
		isRedefined = newIsRedefined;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__IS_REDEFINED, oldIsRedefined, isRedefined));
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
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<BONModel.Class> getAccessors() {
		if (accessors == null) {
			accessors = new EObjectResolvingEList<BONModel.Class>(BONModel.Class.class, this, BONModelPackage.FEATURE__ACCESSORS);
		}
		return accessors;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Parameter> getParameters() {
		if (parameters == null) {
			parameters = new EObjectResolvingEList<Parameter>(Parameter.class, this, BONModelPackage.FEATURE__PARAMETERS);
		}
		return parameters;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Call> getCallsInPrecondition() {
		if (callsInPrecondition == null) {
			callsInPrecondition = new EObjectResolvingEList<Call>(Call.class, this, BONModelPackage.FEATURE__CALLS_IN_PRECONDITION);
		}
		return callsInPrecondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Call> getCallsInPostcondition() {
		if (callsInPostcondition == null) {
			callsInPostcondition = new EObjectResolvingEList<Call>(Call.class, this, BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION);
		}
		return callsInPostcondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Query> getFrame() {
		if (frame == null) {
			frame = new EObjectResolvingEList<Query>(Query.class, this, BONModelPackage.FEATURE__FRAME);
		}
		return frame;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BONModelPackage.FEATURE__IS_DEFERRED:
				return isIsDeferred() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__IS_EFFECTIVE:
				return isIsEffective() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__IS_REDEFINED:
				return isIsRedefined() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__NAME:
				return getName();
			case BONModelPackage.FEATURE__ACCESSORS:
				return getAccessors();
			case BONModelPackage.FEATURE__PARAMETERS:
				return getParameters();
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				return getCallsInPrecondition();
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				return getCallsInPostcondition();
			case BONModelPackage.FEATURE__FRAME:
				return getFrame();
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
			case BONModelPackage.FEATURE__IS_DEFERRED:
				setIsDeferred(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.FEATURE__IS_EFFECTIVE:
				setIsEffective(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.FEATURE__IS_REDEFINED:
				setIsRedefined(((Boolean)newValue).booleanValue());
				return;
			case BONModelPackage.FEATURE__NAME:
				setName((String)newValue);
				return;
			case BONModelPackage.FEATURE__ACCESSORS:
				getAccessors().clear();
				getAccessors().addAll((Collection<? extends BONModel.Class>)newValue);
				return;
			case BONModelPackage.FEATURE__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Parameter>)newValue);
				return;
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				getCallsInPrecondition().clear();
				getCallsInPrecondition().addAll((Collection<? extends Call>)newValue);
				return;
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				getCallsInPostcondition().clear();
				getCallsInPostcondition().addAll((Collection<? extends Call>)newValue);
				return;
			case BONModelPackage.FEATURE__FRAME:
				getFrame().clear();
				getFrame().addAll((Collection<? extends Query>)newValue);
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
			case BONModelPackage.FEATURE__IS_DEFERRED:
				setIsDeferred(IS_DEFERRED_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__IS_EFFECTIVE:
				setIsEffective(IS_EFFECTIVE_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__IS_REDEFINED:
				setIsRedefined(IS_REDEFINED_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__NAME:
				setName(NAME_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__ACCESSORS:
				getAccessors().clear();
				return;
			case BONModelPackage.FEATURE__PARAMETERS:
				getParameters().clear();
				return;
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				getCallsInPrecondition().clear();
				return;
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				getCallsInPostcondition().clear();
				return;
			case BONModelPackage.FEATURE__FRAME:
				getFrame().clear();
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
			case BONModelPackage.FEATURE__IS_DEFERRED:
				return isDeferred != IS_DEFERRED_EDEFAULT;
			case BONModelPackage.FEATURE__IS_EFFECTIVE:
				return isEffective != IS_EFFECTIVE_EDEFAULT;
			case BONModelPackage.FEATURE__IS_REDEFINED:
				return isRedefined != IS_REDEFINED_EDEFAULT;
			case BONModelPackage.FEATURE__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case BONModelPackage.FEATURE__ACCESSORS:
				return accessors != null && !accessors.isEmpty();
			case BONModelPackage.FEATURE__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				return callsInPrecondition != null && !callsInPrecondition.isEmpty();
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				return callsInPostcondition != null && !callsInPostcondition.isEmpty();
			case BONModelPackage.FEATURE__FRAME:
				return frame != null && !frame.isEmpty();
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
		result.append(", isRedefined: ");
		result.append(isRedefined);
		result.append(", name: ");
		result.append(name);
		result.append(')');
		return result.toString();
	}

} //FeatureImpl

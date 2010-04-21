/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.BONModelPackage;
import BONModel.Call;
import BONModel.DoubleStateAssertion;
import BONModel.Feature;
import BONModel.Parameter;
import BONModel.Query;

import BONModel.SingleStateAssertion;
import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

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
 *   <li>{@link BONModel.impl.FeatureImpl#getComment <em>Comment</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getAccessors <em>Accessors</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getCallsInPrecondition <em>Calls In Precondition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getCallsInPostcondition <em>Calls In Postcondition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getFrame <em>Frame</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getPostCondition <em>Post Condition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getPreCondition <em>Pre Condition</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getPreConditionString <em>Pre Condition String</em>}</li>
 *   <li>{@link BONModel.impl.FeatureImpl#getPostConditionString <em>Post Condition String</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class FeatureImpl extends EObjectImpl implements Feature {
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
	 * The default value of the '{@link #getComment() <em>Comment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getComment()
	 * @generated
	 * @ordered
	 */
	protected static final String COMMENT_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getComment() <em>Comment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getComment()
	 * @generated
	 * @ordered
	 */
	protected String comment = COMMENT_EDEFAULT;

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
	 * The cached value of the '{@link #getPostCondition() <em>Post Condition</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPostCondition()
	 * @generated
	 * @ordered
	 */
	protected DoubleStateAssertion postCondition;

	/**
	 * The cached value of the '{@link #getPreCondition() <em>Pre Condition</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPreCondition()
	 * @generated
	 * @ordered
	 */
	protected SingleStateAssertion preCondition;

	/**
	 * The cached value of the '{@link #getParameters() <em>Parameters</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getParameters()
	 * @generated
	 * @ordered
	 */
	protected EList<Parameter> parameters;

	/**
	 * The default value of the '{@link #getPreConditionString() <em>Pre Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPreConditionString()
	 * @generated
	 * @ordered
	 */
	protected static final String PRE_CONDITION_STRING_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getPreConditionString() <em>Pre Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPreConditionString()
	 * @generated
	 * @ordered
	 */
	protected String preConditionString = PRE_CONDITION_STRING_EDEFAULT;

	/**
	 * The default value of the '{@link #getPostConditionString() <em>Post Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPostConditionString()
	 * @generated
	 * @ordered
	 */
	protected static final String POST_CONDITION_STRING_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getPostConditionString() <em>Post Condition String</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPostConditionString()
	 * @generated
	 * @ordered
	 */
	protected String postConditionString = POST_CONDITION_STRING_EDEFAULT;

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
	public String getComment() {
		return comment;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setComment(String newComment) {
		String oldComment = comment;
		comment = newComment;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__COMMENT, oldComment, comment));
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
			parameters = new EObjectContainmentEList<Parameter>(Parameter.class, this, BONModelPackage.FEATURE__PARAMETERS);
		}
		return parameters;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getPreConditionString() {
		return preConditionString;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setPreConditionString(String newPreConditionString) {
		String oldPreConditionString = preConditionString;
		preConditionString = newPreConditionString;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__PRE_CONDITION_STRING, oldPreConditionString, preConditionString));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getPostConditionString() {
		return postConditionString;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setPostConditionString(String newPostConditionString) {
		String oldPostConditionString = postConditionString;
		postConditionString = newPostConditionString;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__POST_CONDITION_STRING, oldPostConditionString, postConditionString));
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
	public DoubleStateAssertion getPostCondition() {
		if (postCondition != null && postCondition.eIsProxy()) {
			InternalEObject oldPostCondition = (InternalEObject)postCondition;
			postCondition = (DoubleStateAssertion)eResolveProxy(oldPostCondition);
			if (postCondition != oldPostCondition) {
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, BONModelPackage.FEATURE__POST_CONDITION, oldPostCondition, postCondition));
			}
		}
		return postCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public DoubleStateAssertion basicGetPostCondition() {
		return postCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setPostCondition(DoubleStateAssertion newPostCondition) {
		DoubleStateAssertion oldPostCondition = postCondition;
		postCondition = newPostCondition;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__POST_CONDITION, oldPostCondition, postCondition));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SingleStateAssertion getPreCondition() {
		if (preCondition != null && preCondition.eIsProxy()) {
			InternalEObject oldPreCondition = (InternalEObject)preCondition;
			preCondition = (SingleStateAssertion)eResolveProxy(oldPreCondition);
			if (preCondition != oldPreCondition) {
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, BONModelPackage.FEATURE__PRE_CONDITION, oldPreCondition, preCondition));
			}
		}
		return preCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SingleStateAssertion basicGetPreCondition() {
		return preCondition;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setPreCondition(SingleStateAssertion newPreCondition) {
		SingleStateAssertion oldPreCondition = preCondition;
		preCondition = newPreCondition;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.FEATURE__PRE_CONDITION, oldPreCondition, preCondition));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void rename(String newName) {
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
			case BONModelPackage.FEATURE__PARAMETERS:
				return ((InternalEList<?>)getParameters()).basicRemove(otherEnd, msgs);
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
			case BONModelPackage.FEATURE__IS_DEFERRED:
				return isIsDeferred() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__IS_EFFECTIVE:
				return isIsEffective() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__IS_REDEFINED:
				return isIsRedefined() ? Boolean.TRUE : Boolean.FALSE;
			case BONModelPackage.FEATURE__NAME:
				return getName();
			case BONModelPackage.FEATURE__COMMENT:
				return getComment();
			case BONModelPackage.FEATURE__ACCESSORS:
				return getAccessors();
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				return getCallsInPrecondition();
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				return getCallsInPostcondition();
			case BONModelPackage.FEATURE__FRAME:
				return getFrame();
			case BONModelPackage.FEATURE__POST_CONDITION:
				if (resolve) return getPostCondition();
				return basicGetPostCondition();
			case BONModelPackage.FEATURE__PRE_CONDITION:
				if (resolve) return getPreCondition();
				return basicGetPreCondition();
			case BONModelPackage.FEATURE__PARAMETERS:
				return getParameters();
			case BONModelPackage.FEATURE__PRE_CONDITION_STRING:
				return getPreConditionString();
			case BONModelPackage.FEATURE__POST_CONDITION_STRING:
				return getPostConditionString();
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
			case BONModelPackage.FEATURE__COMMENT:
				setComment((String)newValue);
				return;
			case BONModelPackage.FEATURE__ACCESSORS:
				getAccessors().clear();
				getAccessors().addAll((Collection<? extends BONModel.Class>)newValue);
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
			case BONModelPackage.FEATURE__POST_CONDITION:
				setPostCondition((DoubleStateAssertion)newValue);
				return;
			case BONModelPackage.FEATURE__PRE_CONDITION:
				setPreCondition((SingleStateAssertion)newValue);
				return;
			case BONModelPackage.FEATURE__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Parameter>)newValue);
				return;
			case BONModelPackage.FEATURE__PRE_CONDITION_STRING:
				setPreConditionString((String)newValue);
				return;
			case BONModelPackage.FEATURE__POST_CONDITION_STRING:
				setPostConditionString((String)newValue);
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
			case BONModelPackage.FEATURE__COMMENT:
				setComment(COMMENT_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__ACCESSORS:
				getAccessors().clear();
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
			case BONModelPackage.FEATURE__POST_CONDITION:
				setPostCondition((DoubleStateAssertion)null);
				return;
			case BONModelPackage.FEATURE__PRE_CONDITION:
				setPreCondition((SingleStateAssertion)null);
				return;
			case BONModelPackage.FEATURE__PARAMETERS:
				getParameters().clear();
				return;
			case BONModelPackage.FEATURE__PRE_CONDITION_STRING:
				setPreConditionString(PRE_CONDITION_STRING_EDEFAULT);
				return;
			case BONModelPackage.FEATURE__POST_CONDITION_STRING:
				setPostConditionString(POST_CONDITION_STRING_EDEFAULT);
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
			case BONModelPackage.FEATURE__COMMENT:
				return COMMENT_EDEFAULT == null ? comment != null : !COMMENT_EDEFAULT.equals(comment);
			case BONModelPackage.FEATURE__ACCESSORS:
				return accessors != null && !accessors.isEmpty();
			case BONModelPackage.FEATURE__CALLS_IN_PRECONDITION:
				return callsInPrecondition != null && !callsInPrecondition.isEmpty();
			case BONModelPackage.FEATURE__CALLS_IN_POSTCONDITION:
				return callsInPostcondition != null && !callsInPostcondition.isEmpty();
			case BONModelPackage.FEATURE__FRAME:
				return frame != null && !frame.isEmpty();
			case BONModelPackage.FEATURE__POST_CONDITION:
				return postCondition != null;
			case BONModelPackage.FEATURE__PRE_CONDITION:
				return preCondition != null;
			case BONModelPackage.FEATURE__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case BONModelPackage.FEATURE__PRE_CONDITION_STRING:
				return PRE_CONDITION_STRING_EDEFAULT == null ? preConditionString != null : !PRE_CONDITION_STRING_EDEFAULT.equals(preConditionString);
			case BONModelPackage.FEATURE__POST_CONDITION_STRING:
				return POST_CONDITION_STRING_EDEFAULT == null ? postConditionString != null : !POST_CONDITION_STRING_EDEFAULT.equals(postConditionString);
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
		result.append(", comment: ");
		result.append(comment);
		result.append(", preConditionString: ");
		result.append(preConditionString);
		result.append(", postConditionString: ");
		result.append(postConditionString);
		result.append(')');
		return result.toString();
	}

} //FeatureImpl

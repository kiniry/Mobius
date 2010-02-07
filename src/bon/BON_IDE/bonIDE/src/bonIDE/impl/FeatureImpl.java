/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.impl;

import bonIDE.BonIDEPackage;
import bonIDE.Feature;

import bonIDE.FeatureArgument;
import bonIDE.PostCondition;
import bonIDE.PreCondition;
import java.util.Collection;
import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;
import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Feature</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link bonIDE.impl.FeatureImpl#getNames <em>Names</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getModifier <em>Modifier</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getType <em>Type</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getComment <em>Comment</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getArguments <em>Arguments</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getPostConditions <em>Post Conditions</em>}</li>
 *   <li>{@link bonIDE.impl.FeatureImpl#getPreConditions <em>Pre Conditions</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class FeatureImpl extends EObjectImpl implements Feature {
	/**
	 * The cached value of the '{@link #getNames() <em>Names</em>}' attribute list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getNames()
	 * @generated
	 * @ordered
	 */
	protected EList<String> names;

	/**
	 * The default value of the '{@link #getModifier() <em>Modifier</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getModifier()
	 * @generated
	 * @ordered
	 */
	protected static final String MODIFIER_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getModifier() <em>Modifier</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getModifier()
	 * @generated
	 * @ordered
	 */
	protected String modifier = MODIFIER_EDEFAULT;

	/**
	 * The default value of the '{@link #getType() <em>Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getType()
	 * @generated
	 * @ordered
	 */
	protected static final String TYPE_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getType() <em>Type</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getType()
	 * @generated
	 * @ordered
	 */
	protected String type = TYPE_EDEFAULT;

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
	 * The cached value of the '{@link #getArguments() <em>Arguments</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getArguments()
	 * @generated
	 * @ordered
	 */
	protected EList<FeatureArgument> arguments;

	/**
	 * The cached value of the '{@link #getPostConditions() <em>Post Conditions</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPostConditions()
	 * @generated
	 * @ordered
	 */
	protected EList<PostCondition> postConditions;

	/**
	 * The cached value of the '{@link #getPreConditions() <em>Pre Conditions</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getPreConditions()
	 * @generated
	 * @ordered
	 */
	protected EList<PreCondition> preConditions;

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
		return BonIDEPackage.Literals.FEATURE;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<String> getNames() {
		if (names == null) {
			names = new EDataTypeUniqueEList<String>(String.class, this, BonIDEPackage.FEATURE__NAMES);
		}
		return names;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getModifier() {
		return modifier;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setModifier(String newModifier) {
		String oldModifier = modifier;
		modifier = newModifier;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.FEATURE__MODIFIER, oldModifier, modifier));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getType() {
		return type;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setType(String newType) {
		String oldType = type;
		type = newType;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.FEATURE__TYPE, oldType, type));
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
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.FEATURE__COMMENT, oldComment, comment));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<FeatureArgument> getArguments() {
		if (arguments == null) {
			arguments = new EObjectContainmentEList<FeatureArgument>(FeatureArgument.class, this, BonIDEPackage.FEATURE__ARGUMENTS);
		}
		return arguments;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<PostCondition> getPostConditions() {
		if (postConditions == null) {
			postConditions = new EObjectContainmentEList<PostCondition>(PostCondition.class, this, BonIDEPackage.FEATURE__POST_CONDITIONS);
		}
		return postConditions;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<PreCondition> getPreConditions() {
		if (preConditions == null) {
			preConditions = new EObjectContainmentEList<PreCondition>(PreCondition.class, this, BonIDEPackage.FEATURE__PRE_CONDITIONS);
		}
		return preConditions;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
		switch (featureID) {
			case BonIDEPackage.FEATURE__ARGUMENTS:
				return ((InternalEList<?>)getArguments()).basicRemove(otherEnd, msgs);
			case BonIDEPackage.FEATURE__POST_CONDITIONS:
				return ((InternalEList<?>)getPostConditions()).basicRemove(otherEnd, msgs);
			case BonIDEPackage.FEATURE__PRE_CONDITIONS:
				return ((InternalEList<?>)getPreConditions()).basicRemove(otherEnd, msgs);
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
			case BonIDEPackage.FEATURE__NAMES:
				return getNames();
			case BonIDEPackage.FEATURE__MODIFIER:
				return getModifier();
			case BonIDEPackage.FEATURE__TYPE:
				return getType();
			case BonIDEPackage.FEATURE__COMMENT:
				return getComment();
			case BonIDEPackage.FEATURE__ARGUMENTS:
				return getArguments();
			case BonIDEPackage.FEATURE__POST_CONDITIONS:
				return getPostConditions();
			case BonIDEPackage.FEATURE__PRE_CONDITIONS:
				return getPreConditions();
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
			case BonIDEPackage.FEATURE__NAMES:
				getNames().clear();
				getNames().addAll((Collection<? extends String>)newValue);
				return;
			case BonIDEPackage.FEATURE__MODIFIER:
				setModifier((String)newValue);
				return;
			case BonIDEPackage.FEATURE__TYPE:
				setType((String)newValue);
				return;
			case BonIDEPackage.FEATURE__COMMENT:
				setComment((String)newValue);
				return;
			case BonIDEPackage.FEATURE__ARGUMENTS:
				getArguments().clear();
				getArguments().addAll((Collection<? extends FeatureArgument>)newValue);
				return;
			case BonIDEPackage.FEATURE__POST_CONDITIONS:
				getPostConditions().clear();
				getPostConditions().addAll((Collection<? extends PostCondition>)newValue);
				return;
			case BonIDEPackage.FEATURE__PRE_CONDITIONS:
				getPreConditions().clear();
				getPreConditions().addAll((Collection<? extends PreCondition>)newValue);
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
			case BonIDEPackage.FEATURE__NAMES:
				getNames().clear();
				return;
			case BonIDEPackage.FEATURE__MODIFIER:
				setModifier(MODIFIER_EDEFAULT);
				return;
			case BonIDEPackage.FEATURE__TYPE:
				setType(TYPE_EDEFAULT);
				return;
			case BonIDEPackage.FEATURE__COMMENT:
				setComment(COMMENT_EDEFAULT);
				return;
			case BonIDEPackage.FEATURE__ARGUMENTS:
				getArguments().clear();
				return;
			case BonIDEPackage.FEATURE__POST_CONDITIONS:
				getPostConditions().clear();
				return;
			case BonIDEPackage.FEATURE__PRE_CONDITIONS:
				getPreConditions().clear();
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
			case BonIDEPackage.FEATURE__NAMES:
				return names != null && !names.isEmpty();
			case BonIDEPackage.FEATURE__MODIFIER:
				return MODIFIER_EDEFAULT == null ? modifier != null : !MODIFIER_EDEFAULT.equals(modifier);
			case BonIDEPackage.FEATURE__TYPE:
				return TYPE_EDEFAULT == null ? type != null : !TYPE_EDEFAULT.equals(type);
			case BonIDEPackage.FEATURE__COMMENT:
				return COMMENT_EDEFAULT == null ? comment != null : !COMMENT_EDEFAULT.equals(comment);
			case BonIDEPackage.FEATURE__ARGUMENTS:
				return arguments != null && !arguments.isEmpty();
			case BonIDEPackage.FEATURE__POST_CONDITIONS:
				return postConditions != null && !postConditions.isEmpty();
			case BonIDEPackage.FEATURE__PRE_CONDITIONS:
				return preConditions != null && !preConditions.isEmpty();
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
		result.append(" (names: ");
		result.append(names);
		result.append(", modifier: ");
		result.append(modifier);
		result.append(", type: ");
		result.append(type);
		result.append(", comment: ");
		result.append(comment);
		result.append(')');
		return result.toString();
	}

} //FeatureImpl

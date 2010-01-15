/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.impl;

import bonIDE.BonIDEPackage;
import bonIDE.Cluster;
import bonIDE.StaticAbstraction;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Cluster</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link bonIDE.impl.ClusterImpl#getContents <em>Contents</em>}</li>
 *   <li>{@link bonIDE.impl.ClusterImpl#getName <em>Name</em>}</li>
 *   <li>{@link bonIDE.impl.ClusterImpl#isCollapsed <em>Collapsed</em>}</li>
 *   <li>{@link bonIDE.impl.ClusterImpl#getExpandedHeight <em>Expanded Height</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ClusterImpl extends StaticAbstractionImpl implements Cluster {
	/**
	 * The cached value of the '{@link #getContents() <em>Contents</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getContents()
	 * @generated
	 * @ordered
	 */
	protected EList<StaticAbstraction> contents;

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
	 * The default value of the '{@link #isCollapsed() <em>Collapsed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isCollapsed()
	 * @generated
	 * @ordered
	 */
	protected static final boolean COLLAPSED_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isCollapsed() <em>Collapsed</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isCollapsed()
	 * @generated
	 * @ordered
	 */
	protected boolean collapsed = COLLAPSED_EDEFAULT;

	/**
	 * The default value of the '{@link #getExpandedHeight() <em>Expanded Height</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getExpandedHeight()
	 * @generated
	 * @ordered
	 */
	protected static final int EXPANDED_HEIGHT_EDEFAULT = 0;

	/**
	 * The cached value of the '{@link #getExpandedHeight() <em>Expanded Height</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getExpandedHeight()
	 * @generated
	 * @ordered
	 */
	protected int expandedHeight = EXPANDED_HEIGHT_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ClusterImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BonIDEPackage.Literals.CLUSTER;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<StaticAbstraction> getContents() {
		if (contents == null) {
			contents = new EObjectContainmentEList<StaticAbstraction>(StaticAbstraction.class, this, BonIDEPackage.CLUSTER__CONTENTS);
		}
		return contents;
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
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.CLUSTER__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isCollapsed() {
		return collapsed;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setCollapsed(boolean newCollapsed) {
		boolean oldCollapsed = collapsed;
		collapsed = newCollapsed;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.CLUSTER__COLLAPSED, oldCollapsed, collapsed));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public int getExpandedHeight() {
		return expandedHeight;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setExpandedHeight(int newExpandedHeight) {
		int oldExpandedHeight = expandedHeight;
		expandedHeight = newExpandedHeight;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BonIDEPackage.CLUSTER__EXPANDED_HEIGHT, oldExpandedHeight, expandedHeight));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
		switch (featureID) {
			case BonIDEPackage.CLUSTER__CONTENTS:
				return ((InternalEList<?>)getContents()).basicRemove(otherEnd, msgs);
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
			case BonIDEPackage.CLUSTER__CONTENTS:
				return getContents();
			case BonIDEPackage.CLUSTER__NAME:
				return getName();
			case BonIDEPackage.CLUSTER__COLLAPSED:
				return isCollapsed();
			case BonIDEPackage.CLUSTER__EXPANDED_HEIGHT:
				return getExpandedHeight();
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
			case BonIDEPackage.CLUSTER__CONTENTS:
				getContents().clear();
				getContents().addAll((Collection<? extends StaticAbstraction>)newValue);
				return;
			case BonIDEPackage.CLUSTER__NAME:
				setName((String)newValue);
				return;
			case BonIDEPackage.CLUSTER__COLLAPSED:
				setCollapsed((Boolean)newValue);
				return;
			case BonIDEPackage.CLUSTER__EXPANDED_HEIGHT:
				setExpandedHeight((Integer)newValue);
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
			case BonIDEPackage.CLUSTER__CONTENTS:
				getContents().clear();
				return;
			case BonIDEPackage.CLUSTER__NAME:
				setName(NAME_EDEFAULT);
				return;
			case BonIDEPackage.CLUSTER__COLLAPSED:
				setCollapsed(COLLAPSED_EDEFAULT);
				return;
			case BonIDEPackage.CLUSTER__EXPANDED_HEIGHT:
				setExpandedHeight(EXPANDED_HEIGHT_EDEFAULT);
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
			case BonIDEPackage.CLUSTER__CONTENTS:
				return contents != null && !contents.isEmpty();
			case BonIDEPackage.CLUSTER__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case BonIDEPackage.CLUSTER__COLLAPSED:
				return collapsed != COLLAPSED_EDEFAULT;
			case BonIDEPackage.CLUSTER__EXPANDED_HEIGHT:
				return expandedHeight != EXPANDED_HEIGHT_EDEFAULT;
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
		result.append(", collapsed: ");
		result.append(collapsed);
		result.append(", expandedHeight: ");
		result.append(expandedHeight);
		result.append(')');
		return result.toString();
	}

} //ClusterImpl

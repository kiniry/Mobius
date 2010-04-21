/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.BONModelPackage;
import BONModel.Call;
import BONModel.ChainedCall;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Chained Call</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link BONModel.impl.ChainedCallImpl#getChain <em>Chain</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ChainedCallImpl extends CallImpl implements ChainedCall {
	/**
	 * The cached value of the '{@link #getChain() <em>Chain</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getChain()
	 * @generated
	 * @ordered
	 */
	protected Call chain;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ChainedCallImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return BONModelPackage.Literals.CHAINED_CALL;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Call getChain() {
		if (chain != null && chain.eIsProxy()) {
			InternalEObject oldChain = (InternalEObject)chain;
			chain = (Call)eResolveProxy(oldChain);
			if (chain != oldChain) {
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, BONModelPackage.CHAINED_CALL__CHAIN, oldChain, chain));
			}
		}
		return chain;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Call basicGetChain() {
		return chain;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setChain(Call newChain) {
		Call oldChain = chain;
		chain = newChain;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, BONModelPackage.CHAINED_CALL__CHAIN, oldChain, chain));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case BONModelPackage.CHAINED_CALL__CHAIN:
				if (resolve) return getChain();
				return basicGetChain();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
			case BONModelPackage.CHAINED_CALL__CHAIN:
				setChain((Call)newValue);
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
			case BONModelPackage.CHAINED_CALL__CHAIN:
				setChain((Call)null);
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
			case BONModelPackage.CHAINED_CALL__CHAIN:
				return chain != null;
		}
		return super.eIsSet(featureID);
	}

} //ChainedCallImpl

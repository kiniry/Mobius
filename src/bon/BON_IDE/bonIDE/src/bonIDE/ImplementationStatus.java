/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.Enumerator;

/**
 * <!-- begin-user-doc -->
 * A representation of the literals of the enumeration '<em><b>Implementation Status</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see bonIDE.BonIDEPackage#getImplementationStatus()
 * @model
 * @generated
 */
public enum ImplementationStatus implements Enumerator {
	/**
	 * The '<em><b>Reused</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #REUSED_VALUE
	 * @generated
	 * @ordered
	 */
	REUSED(0, "Reused", "Reused"),

	/**
	 * The '<em><b>Persistent</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #PERSISTENT_VALUE
	 * @generated
	 * @ordered
	 */
	PERSISTENT(1, "Persistent", "Persistent"),

	/**
	 * The '<em><b>Deferred</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #DEFERRED_VALUE
	 * @generated
	 * @ordered
	 */
	DEFERRED(2, "Deferred", "Deferred"),

	/**
	 * The '<em><b>Effective</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #EFFECTIVE_VALUE
	 * @generated
	 * @ordered
	 */
	EFFECTIVE(3, "Effective", "Effective"),

	/**
	 * The '<em><b>Interfaced</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #INTERFACED_VALUE
	 * @generated
	 * @ordered
	 */
	INTERFACED(4, "Interfaced", "Interfaced"),

	/**
	 * The '<em><b>Root</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #ROOT_VALUE
	 * @generated
	 * @ordered
	 */
	ROOT(5, "Root", "Root"), /**
	 * The '<em><b>Parameterized</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #PARAMETERIZED_VALUE
	 * @generated
	 * @ordered
	 */
	PARAMETERIZED(6, "Parameterized", "Parameterized");

	/**
	 * The '<em><b>Reused</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Reused</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #REUSED
	 * @model name="Reused"
	 * @generated
	 * @ordered
	 */
	public static final int REUSED_VALUE = 0;

	/**
	 * The '<em><b>Persistent</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Persistent</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #PERSISTENT
	 * @model name="Persistent"
	 * @generated
	 * @ordered
	 */
	public static final int PERSISTENT_VALUE = 1;

	/**
	 * The '<em><b>Deferred</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Deferred</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #DEFERRED
	 * @model name="Deferred"
	 * @generated
	 * @ordered
	 */
	public static final int DEFERRED_VALUE = 2;

	/**
	 * The '<em><b>Effective</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Effective</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #EFFECTIVE
	 * @model name="Effective"
	 * @generated
	 * @ordered
	 */
	public static final int EFFECTIVE_VALUE = 3;

	/**
	 * The '<em><b>Interfaced</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Interfaced</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #INTERFACED
	 * @model name="Interfaced"
	 * @generated
	 * @ordered
	 */
	public static final int INTERFACED_VALUE = 4;

	/**
	 * The '<em><b>Root</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Root</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #ROOT
	 * @model name="Root"
	 * @generated
	 * @ordered
	 */
	public static final int ROOT_VALUE = 5;

	/**
	 * The '<em><b>Parameterized</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>Parameterized</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #PARAMETERIZED
	 * @model name="Parameterized"
	 * @generated
	 * @ordered
	 */
	public static final int PARAMETERIZED_VALUE = 6;

	/**
	 * An array of all the '<em><b>Implementation Status</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private static final ImplementationStatus[] VALUES_ARRAY =
		new ImplementationStatus[] {
			REUSED,
			PERSISTENT,
			DEFERRED,
			EFFECTIVE,
			INTERFACED,
			ROOT,
			PARAMETERIZED,
		};

	/**
	 * A public read-only list of all the '<em><b>Implementation Status</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final List<ImplementationStatus> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

	/**
	 * Returns the '<em><b>Implementation Status</b></em>' literal with the specified literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static ImplementationStatus get(String literal) {
		for (int i = 0; i < VALUES_ARRAY.length; ++i) {
			ImplementationStatus result = VALUES_ARRAY[i];
			if (result.toString().equals(literal)) {
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Implementation Status</b></em>' literal with the specified name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static ImplementationStatus getByName(String name) {
		for (int i = 0; i < VALUES_ARRAY.length; ++i) {
			ImplementationStatus result = VALUES_ARRAY[i];
			if (result.getName().equals(name)) {
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Implementation Status</b></em>' literal with the specified integer value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static ImplementationStatus get(int value) {
		switch (value) {
			case REUSED_VALUE: return REUSED;
			case PERSISTENT_VALUE: return PERSISTENT;
			case DEFERRED_VALUE: return DEFERRED;
			case EFFECTIVE_VALUE: return EFFECTIVE;
			case INTERFACED_VALUE: return INTERFACED;
			case ROOT_VALUE: return ROOT;
			case PARAMETERIZED_VALUE: return PARAMETERIZED;
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final int value;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String name;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String literal;

	/**
	 * Only this class can construct instances.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private ImplementationStatus(int value, String name, String literal) {
		this.value = value;
		this.name = name;
		this.literal = literal;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public int getValue() {
	  return value;
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
	public String getLiteral() {
	  return literal;
	}

	/**
	 * Returns the literal value of the enumerator, which is its string representation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString() {
		return literal;
	}
	
} //ImplementationStatus

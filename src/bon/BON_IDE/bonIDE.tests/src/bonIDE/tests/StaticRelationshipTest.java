/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.tests;

import bonIDE.BonIDEFactory;
import bonIDE.StaticRelationship;

import junit.framework.TestCase;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Static Relationship</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class StaticRelationshipTest extends TestCase {

	/**
	 * The fixture for this Static Relationship test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected StaticRelationship fixture = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static void main(String[] args) {
		TestRunner.run(StaticRelationshipTest.class);
	}

	/**
	 * Constructs a new Static Relationship test case with the given name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public StaticRelationshipTest(String name) {
		super(name);
	}

	/**
	 * Sets the fixture for this Static Relationship test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected void setFixture(StaticRelationship fixture) {
		this.fixture = fixture;
	}

	/**
	 * Returns the fixture for this Static Relationship test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected StaticRelationship getFixture() {
		return fixture;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#setUp()
	 * @generated
	 */
	@Override
	protected void setUp() throws Exception {
		setFixture(BonIDEFactory.eINSTANCE.createStaticRelationship());
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#tearDown()
	 * @generated
	 */
	@Override
	protected void tearDown() throws Exception {
		setFixture(null);
	}

} //StaticRelationshipTest

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.tests;

import bonIDE.BonIDEFactory;
import bonIDE.InheritanceRel;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Inheritance Rel</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class InheritanceRelTest extends StaticRelationshipTest {

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static void main(String[] args) {
		TestRunner.run(InheritanceRelTest.class);
	}

	/**
	 * Constructs a new Inheritance Rel test case with the given name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InheritanceRelTest(String name) {
		super(name);
	}

	/**
	 * Returns the fixture for this Inheritance Rel test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected InheritanceRel getFixture() {
		return (InheritanceRel)fixture;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#setUp()
	 * @generated
	 */
	@Override
	protected void setUp() throws Exception {
		setFixture(BonIDEFactory.eINSTANCE.createInheritanceRel());
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

} //InheritanceRelTest

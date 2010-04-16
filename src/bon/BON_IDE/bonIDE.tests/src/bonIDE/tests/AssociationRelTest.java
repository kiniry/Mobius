/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.tests;

import bonIDE.AssociationRel;
import bonIDE.BonIDEFactory;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Association Rel</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class AssociationRelTest extends ClientSupplierRelTest {

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static void main(String[] args) {
		TestRunner.run(AssociationRelTest.class);
	}

	/**
	 * Constructs a new Association Rel test case with the given name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AssociationRelTest(String name) {
		super(name);
	}

	/**
	 * Returns the fixture for this Association Rel test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected AssociationRel getFixture() {
		return (AssociationRel)fixture;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#setUp()
	 * @generated
	 */
	@Override
	protected void setUp() throws Exception {
		setFixture(BonIDEFactory.eINSTANCE.createAssociationRel());
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

} //AssociationRelTest

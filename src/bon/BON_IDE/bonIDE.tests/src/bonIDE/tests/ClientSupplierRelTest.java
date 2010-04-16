/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.tests;

import bonIDE.BonIDEFactory;
import bonIDE.ClientSupplierRel;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Client Supplier Rel</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class ClientSupplierRelTest extends StaticRelationshipTest {

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static void main(String[] args) {
		TestRunner.run(ClientSupplierRelTest.class);
	}

	/**
	 * Constructs a new Client Supplier Rel test case with the given name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ClientSupplierRelTest(String name) {
		super(name);
	}

	/**
	 * Returns the fixture for this Client Supplier Rel test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected ClientSupplierRel getFixture() {
		return (ClientSupplierRel)fixture;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#setUp()
	 * @generated
	 */
	@Override
	protected void setUp() throws Exception {
		setFixture(BonIDEFactory.eINSTANCE.createClientSupplierRel());
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

} //ClientSupplierRelTest

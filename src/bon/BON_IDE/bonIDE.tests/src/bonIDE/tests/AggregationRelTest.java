/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.tests;

import bonIDE.AggregationRel;
import bonIDE.BonIDEFactory;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Aggregation Rel</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class AggregationRelTest extends ClientSupplierRelTest {

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static void main(String[] args) {
		TestRunner.run(AggregationRelTest.class);
	}

	/**
	 * Constructs a new Aggregation Rel test case with the given name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AggregationRelTest(String name) {
		super(name);
	}

	/**
	 * Returns the fixture for this Aggregation Rel test case.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected AggregationRel getFixture() {
		return (AggregationRel)fixture;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see junit.framework.TestCase#setUp()
	 * @generated
	 */
	@Override
	protected void setUp() throws Exception {
		setFixture(BonIDEFactory.eINSTANCE.createAggregationRel());
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

} //AggregationRelTest

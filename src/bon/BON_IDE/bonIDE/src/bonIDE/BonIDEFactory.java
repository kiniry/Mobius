/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see bonIDE.BonIDEPackage
 * @generated
 */
public interface BonIDEFactory extends EFactory {
	/**
	 * The singleton instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	BonIDEFactory eINSTANCE = bonIDE.impl.BonIDEFactoryImpl.init();

	/**
	 * Returns a new object of class '<em>Model</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Model</em>'.
	 * @generated
	 */
	Model createModel();

	/**
	 * Returns a new object of class '<em>Cluster</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Cluster</em>'.
	 * @generated
	 */
	Cluster createCluster();

	/**
	 * Returns a new object of class '<em>BON Class</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>BON Class</em>'.
	 * @generated
	 */
	BONClass createBONClass();

	/**
	 * Returns a new object of class '<em>Feature</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Feature</em>'.
	 * @generated
	 */
	Feature createFeature();

	/**
	 * Returns a new object of class '<em>Index Clause</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Index Clause</em>'.
	 * @generated
	 */
	IndexClause createIndexClause();

	/**
	 * Returns a new object of class '<em>Inheritance Clause</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Inheritance Clause</em>'.
	 * @generated
	 */
	InheritanceClause createInheritanceClause();

	/**
	 * Returns a new object of class '<em>Feature Argument</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Feature Argument</em>'.
	 * @generated
	 */
	FeatureArgument createFeatureArgument();

	/**
	 * Returns a new object of class '<em>Pre Condition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Pre Condition</em>'.
	 * @generated
	 */
	PreCondition createPreCondition();

	/**
	 * Returns a new object of class '<em>Post Condition</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Post Condition</em>'.
	 * @generated
	 */
	PostCondition createPostCondition();

	/**
	 * Returns a new object of class '<em>Invariant</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Invariant</em>'.
	 * @generated
	 */
	Invariant createInvariant();

	/**
	 * Returns a new object of class '<em>Static Relationship</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Static Relationship</em>'.
	 * @generated
	 */
	StaticRelationship createStaticRelationship();

	/**
	 * Returns a new object of class '<em>Inheritance Rel</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Inheritance Rel</em>'.
	 * @generated
	 */
	InheritanceRel createInheritanceRel();

	/**
	 * Returns a new object of class '<em>Client Supplier Rel</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Client Supplier Rel</em>'.
	 * @generated
	 */
	ClientSupplierRel createClientSupplierRel();

	/**
	 * Returns a new object of class '<em>Aggregation Rel</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Aggregation Rel</em>'.
	 * @generated
	 */
	AggregationRel createAggregationRel();

	/**
	 * Returns a new object of class '<em>Association Rel</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Association Rel</em>'.
	 * @generated
	 */
	AssociationRel createAssociationRel();

	/**
	 * Returns the package supported by this factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the package supported by this factory.
	 * @generated
	 */
	BonIDEPackage getBonIDEPackage();

} //BonIDEFactory

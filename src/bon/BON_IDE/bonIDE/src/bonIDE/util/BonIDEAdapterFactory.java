/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package bonIDE.util;

import bonIDE.*;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see bonIDE.BonIDEPackage
 * @generated
 */
public class BonIDEAdapterFactory extends AdapterFactoryImpl {
	/**
	 * The cached model package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected static BonIDEPackage modelPackage;

	/**
	 * Creates an instance of the adapter factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BonIDEAdapterFactory() {
		if (modelPackage == null) {
			modelPackage = BonIDEPackage.eINSTANCE;
		}
	}

	/**
	 * Returns whether this factory is applicable for the type of the object.
	 * <!-- begin-user-doc -->
	 * This implementation returns <code>true</code> if the object is either the model's package or is an instance object of the model.
	 * <!-- end-user-doc -->
	 * @return whether this factory is applicable for the type of the object.
	 * @generated
	 */
	@Override
	public boolean isFactoryForType(Object object) {
		if (object == modelPackage) {
			return true;
		}
		if (object instanceof EObject) {
			return ((EObject)object).eClass().getEPackage() == modelPackage;
		}
		return false;
	}

	/**
	 * The switch that delegates to the <code>createXXX</code> methods.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected BonIDESwitch<Adapter> modelSwitch =
		new BonIDESwitch<Adapter>() {
			@Override
			public Adapter caseModel(Model object) {
				return createModelAdapter();
			}
			@Override
			public Adapter caseAbstraction(Abstraction object) {
				return createAbstractionAdapter();
			}
			@Override
			public Adapter caseCluster(Cluster object) {
				return createClusterAdapter();
			}
			@Override
			public Adapter caseBONClass(BONClass object) {
				return createBONClassAdapter();
			}
			@Override
			public Adapter caseStaticAbstraction(StaticAbstraction object) {
				return createStaticAbstractionAdapter();
			}
			@Override
			public Adapter caseFeature(Feature object) {
				return createFeatureAdapter();
			}
			@Override
			public Adapter caseIndexClause(IndexClause object) {
				return createIndexClauseAdapter();
			}
			@Override
			public Adapter caseInheritanceClause(InheritanceClause object) {
				return createInheritanceClauseAdapter();
			}
			@Override
			public Adapter caseFeatureArgument(FeatureArgument object) {
				return createFeatureArgumentAdapter();
			}
			@Override
			public Adapter casePreCondition(PreCondition object) {
				return createPreConditionAdapter();
			}
			@Override
			public Adapter casePostCondition(PostCondition object) {
				return createPostConditionAdapter();
			}
			@Override
			public Adapter caseInvariant(Invariant object) {
				return createInvariantAdapter();
			}
			@Override
			public Adapter caseStaticRelationship(StaticRelationship object) {
				return createStaticRelationshipAdapter();
			}
			@Override
			public Adapter caseInheritanceRel(InheritanceRel object) {
				return createInheritanceRelAdapter();
			}
			@Override
			public Adapter caseClientSupplierRel(ClientSupplierRel object) {
				return createClientSupplierRelAdapter();
			}
			@Override
			public Adapter caseAggregationRel(AggregationRel object) {
				return createAggregationRelAdapter();
			}
			@Override
			public Adapter caseAssociationRel(AssociationRel object) {
				return createAssociationRelAdapter();
			}
			@Override
			public Adapter defaultCase(EObject object) {
				return createEObjectAdapter();
			}
		};

	/**
	 * Creates an adapter for the <code>target</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param target the object to adapt.
	 * @return the adapter for the <code>target</code>.
	 * @generated
	 */
	@Override
	public Adapter createAdapter(Notifier target) {
		return modelSwitch.doSwitch((EObject)target);
	}


	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.Model <em>Model</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.Model
	 * @generated
	 */
	public Adapter createModelAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.Abstraction <em>Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.Abstraction
	 * @generated
	 */
	public Adapter createAbstractionAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.Cluster <em>Cluster</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.Cluster
	 * @generated
	 */
	public Adapter createClusterAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.BONClass <em>BON Class</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.BONClass
	 * @generated
	 */
	public Adapter createBONClassAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.StaticAbstraction <em>Static Abstraction</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.StaticAbstraction
	 * @generated
	 */
	public Adapter createStaticAbstractionAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.Feature <em>Feature</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.Feature
	 * @generated
	 */
	public Adapter createFeatureAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.IndexClause <em>Index Clause</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.IndexClause
	 * @generated
	 */
	public Adapter createIndexClauseAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.InheritanceClause <em>Inheritance Clause</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.InheritanceClause
	 * @generated
	 */
	public Adapter createInheritanceClauseAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.FeatureArgument <em>Feature Argument</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.FeatureArgument
	 * @generated
	 */
	public Adapter createFeatureArgumentAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.PreCondition <em>Pre Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.PreCondition
	 * @generated
	 */
	public Adapter createPreConditionAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.PostCondition <em>Post Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.PostCondition
	 * @generated
	 */
	public Adapter createPostConditionAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.Invariant <em>Invariant</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.Invariant
	 * @generated
	 */
	public Adapter createInvariantAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.StaticRelationship <em>Static Relationship</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.StaticRelationship
	 * @generated
	 */
	public Adapter createStaticRelationshipAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.InheritanceRel <em>Inheritance Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.InheritanceRel
	 * @generated
	 */
	public Adapter createInheritanceRelAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.ClientSupplierRel <em>Client Supplier Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.ClientSupplierRel
	 * @generated
	 */
	public Adapter createClientSupplierRelAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.AggregationRel <em>Aggregation Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.AggregationRel
	 * @generated
	 */
	public Adapter createAggregationRelAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for an object of class '{@link bonIDE.AssociationRel <em>Association Rel</em>}'.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null so that we can easily ignore cases;
	 * it's useful to ignore a case when inheritance will catch all the cases anyway.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @see bonIDE.AssociationRel
	 * @generated
	 */
	public Adapter createAssociationRelAdapter() {
		return null;
	}

	/**
	 * Creates a new adapter for the default case.
	 * <!-- begin-user-doc -->
	 * This default implementation returns null.
	 * <!-- end-user-doc -->
	 * @return the new adapter.
	 * @generated
	 */
	public Adapter createEObjectAdapter() {
		return null;
	}

} //BonIDEAdapterFactory

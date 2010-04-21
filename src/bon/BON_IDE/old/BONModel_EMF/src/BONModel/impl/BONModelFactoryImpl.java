/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package BONModel.impl;

import BONModel.Aggregation;
import BONModel.Assertion;
import BONModel.Association;
import BONModel.BONModelFactory;
import BONModel.BONModelPackage;
import BONModel.BooleanExpression;
import BONModel.ChainedCall;
import BONModel.Cluster;
import BONModel.Command;
import BONModel.DirectCall;
import BONModel.DoubleStateAssertion;
import BONModel.DynamicAbstraction;
import BONModel.Entity;
import BONModel.Expression;
import BONModel.Feature;
import BONModel.Inheritance;
import BONModel.Message;
import BONModel.Model;
import BONModel.ObjectCluster;
import BONModel.Parameter;
import BONModel.Query;
import BONModel.RelationshipType;
import BONModel.Renaming;

import BONModel.SingleStateAssertion;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class BONModelFactoryImpl extends EFactoryImpl implements BONModelFactory {
	/**
	 * Creates the default factory implementation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static BONModelFactory init() {
		try {
			BONModelFactory theBONModelFactory = (BONModelFactory)EPackage.Registry.INSTANCE.getEFactory("www.ucd.ie/BONModel"); 
			if (theBONModelFactory != null) {
				return theBONModelFactory;
			}
		}
		catch (Exception exception) {
			EcorePlugin.INSTANCE.log(exception);
		}
		return new BONModelFactoryImpl();
	}

	/**
	 * Creates an instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BONModelFactoryImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EObject create(EClass eClass) {
		switch (eClass.getClassifierID()) {
			case BONModelPackage.MODEL: return createModel();
			case BONModelPackage.INHERITANCE: return createInheritance();
			case BONModelPackage.AGGREGATION: return createAggregation();
			case BONModelPackage.ASSOCIATION: return createAssociation();
			case BONModelPackage.MESSAGE: return createMessage();
			case BONModelPackage.CLUSTER: return createCluster();
			case BONModelPackage.CLASS: return createClass();
			case BONModelPackage.RENAMING: return createRenaming();
			case BONModelPackage.DYNAMIC_ABSTRACTION: return createDynamicAbstraction();
			case BONModelPackage.OBJECT: return createObject();
			case BONModelPackage.OBJECT_CLUSTER: return createObjectCluster();
			case BONModelPackage.COMMAND: return createCommand();
			case BONModelPackage.QUERY: return createQuery();
			case BONModelPackage.PARAMETER: return createParameter();
			case BONModelPackage.DIRECT_CALL: return createDirectCall();
			case BONModelPackage.CHAINED_CALL: return createChainedCall();
			case BONModelPackage.EXPRESSION: return createExpression();
			case BONModelPackage.BOOLEAN_EXPRESSION: return createBooleanExpression();
			case BONModelPackage.ASSERTION: return createAssertion();
			case BONModelPackage.SINGLE_STATE_ASSERTION: return createSingleStateAssertion();
			case BONModelPackage.DOUBLE_STATE_ASSERTION: return createDoubleStateAssertion();
			case BONModelPackage.ENTITY: return createEntity();
			default:
				throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object createFromString(EDataType eDataType, String initialValue) {
		switch (eDataType.getClassifierID()) {
			case BONModelPackage.RELATIONSHIP_TYPE:
				return createRelationshipTypeFromString(eDataType, initialValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String convertToString(EDataType eDataType, Object instanceValue) {
		switch (eDataType.getClassifierID()) {
			case BONModelPackage.RELATIONSHIP_TYPE:
				return convertRelationshipTypeToString(eDataType, instanceValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Model createModel() {
		ModelImpl model = new ModelImpl();
		return model;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Inheritance createInheritance() {
		InheritanceImpl inheritance = new InheritanceImpl();
		return inheritance;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Aggregation createAggregation() {
		AggregationImpl aggregation = new AggregationImpl();
		return aggregation;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Association createAssociation() {
		AssociationImpl association = new AssociationImpl();
		return association;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Message createMessage() {
		MessageImpl message = new MessageImpl();
		return message;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Cluster createCluster() {
		ClusterImpl cluster = new ClusterImpl();
		return cluster;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BONModel.Class createClass() {
		ClassImpl class_ = new ClassImpl();
		return class_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Renaming createRenaming() {
		RenamingImpl renaming = new RenamingImpl();
		return renaming;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public DynamicAbstraction createDynamicAbstraction() {
		DynamicAbstractionImpl dynamicAbstraction = new DynamicAbstractionImpl();
		return dynamicAbstraction;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BONModel.Object createObject() {
		ObjectImpl object = new ObjectImpl();
		return object;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ObjectCluster createObjectCluster() {
		ObjectClusterImpl objectCluster = new ObjectClusterImpl();
		return objectCluster;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Command createCommand() {
		CommandImpl command = new CommandImpl();
		return command;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Query createQuery() {
		QueryImpl query = new QueryImpl();
		return query;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Parameter createParameter() {
		ParameterImpl parameter = new ParameterImpl();
		return parameter;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public DirectCall createDirectCall() {
		DirectCallImpl directCall = new DirectCallImpl();
		return directCall;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ChainedCall createChainedCall() {
		ChainedCallImpl chainedCall = new ChainedCallImpl();
		return chainedCall;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Expression createExpression() {
		ExpressionImpl expression = new ExpressionImpl();
		return expression;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BooleanExpression createBooleanExpression() {
		BooleanExpressionImpl booleanExpression = new BooleanExpressionImpl();
		return booleanExpression;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Assertion createAssertion() {
		AssertionImpl assertion = new AssertionImpl();
		return assertion;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SingleStateAssertion createSingleStateAssertion() {
		SingleStateAssertionImpl singleStateAssertion = new SingleStateAssertionImpl();
		return singleStateAssertion;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public DoubleStateAssertion createDoubleStateAssertion() {
		DoubleStateAssertionImpl doubleStateAssertion = new DoubleStateAssertionImpl();
		return doubleStateAssertion;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Entity createEntity() {
		EntityImpl entity = new EntityImpl();
		return entity;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public RelationshipType createRelationshipTypeFromString(EDataType eDataType, String initialValue) {
		RelationshipType result = RelationshipType.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertRelationshipTypeToString(EDataType eDataType, Object instanceValue) {
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BONModelPackage getBONModelPackage() {
		return (BONModelPackage)getEPackage();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @deprecated
	 * @generated
	 */
	@Deprecated
	public static BONModelPackage getPackage() {
		return BONModelPackage.eINSTANCE;
	}

} //BONModelFactoryImpl

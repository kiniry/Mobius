package bonIDE.diagram.custom;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.command.SetCommand;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.commands.CompoundCommand;
import org.eclipse.gef.editparts.AbstractEditPart;
import org.eclipse.gmf.runtime.common.core.command.ICommand;
import org.eclipse.gmf.runtime.diagram.core.internal.commands.PersistViewsCommand;
import org.eclipse.gmf.runtime.diagram.core.util.ViewUtil;
import org.eclipse.gmf.runtime.diagram.ui.commands.DeferredCreateConnectionViewAndElementCommand;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramCommandStack;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateConnectionViewAndElementRequest;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateViewRequest;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IHintedType;
import org.eclipse.gmf.runtime.emf.type.core.commands.SetValueCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.SetRequest;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Shell;
import org.w3c.dom.Node;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import com.google.common.collect.Multimap;

import bonIDE.Abstraction;
import bonIDE.BONClass;
import bonIDE.StaticAbstraction;
import bonIDE.diagram.edit.parts.BONClass2EditPart;
import bonIDE.diagram.edit.parts.BONClassEditPart;
import bonIDE.diagram.edit.parts.BONClassName2EditPart;
import bonIDE.diagram.edit.parts.BONClassNameEditPart;
import bonIDE.diagram.edit.parts.ClusterEditPart;
import bonIDE.diagram.edit.parts.ModelEditPart;
import bonIDE.diagram.providers.BonideElementTypes;
import bonIDE.impl.BONClassImpl;
import bonIDE.impl.BonIDEFactoryImpl;
import bonIDE.impl.ClusterImpl;
import bonIDE.impl.FeatureImpl;
import bonIDE.impl.ModelImpl;
import bonIDE.BonIDEPackage;

import ie.ucd.bon.API;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.FeatureSpecification.Modifier;
import ie.ucd.bon.ast.TypeMark.Mark;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.PrettyPrintVisitor;
import ie.ucd.bon.source.SourceReader;
import ie.ucd.bon.typechecker.BONST;

public class BonDiagramElementBuilder implements IRunnableWithProgress {

	private ModelEditPart modelEP;
	private String bonFileName;

	public BonDiagramElementBuilder(String fileName, ModelEditPart modelEditPart) {
		this.modelEP = modelEditPart;
		this.bonFileName = fileName;
	}

	public static void createBONStaticDiagram(String fileName, ModelEditPart modelEP, Shell windowShell) {
		try {
			IRunnableWithProgress diagramBuildOperation = new BonDiagramElementBuilder(fileName, modelEP);
			// TODO: explain
			new ProgressMonitorDialog(windowShell).run(true, true, diagramBuildOperation);
		} catch (InvocationTargetException e) {
			// TODO:handle exception
		} catch (InterruptedException e) {
			// TODO: handle cancellation
		}

		persistAllElements(modelEP.getDiagramView());
	}

	public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {

		monitor.setTaskName("Building diagram...");
		monitor.subTask("Loading bon source file...");

		List<File> files = new ArrayList<File>();
		files.add(new File(bonFileName));
		ParsingTracker bonTracker = null;
		BONST bonST = null;

		try {
			bonTracker = API.parse(files, false, false);
			bonST = bonTracker.getSymbolTable();
		} catch (Exception ex) {
			throw new InterruptedException("Failed to parse file " + bonFileName + ".");
		}

		for (ParseResult result : bonTracker.getParses()) {
			if (result.isValidParse() == false) {
				throw new InterruptedException("Failed to parse file " + bonFileName + ".");
			}
		}

		monitor.subTask("Loading bon source file...done.");

		for (Cluster cluster : bonST.clusters.values()) {

			bonIDE.Cluster newCluster = createBONClusterElement(cluster);

			Multimap<Cluster, String> reverseMap = bonST.classClusterMap.reverse();
			Collection<String> componentsInCluster = reverseMap.get(cluster);
			Object componentNode = null;
			BONClass newClass = null;

			for (String componentName : componentsInCluster) {

				componentNode = bonST.classes.get(componentName);

				if (componentNode instanceof ie.ucd.bon.ast.Clazz) {
					monitor.subTask("Creating class " + ((Clazz) componentNode).name.name + ".");
					newClass = createBONClassElement((Clazz) componentNode);
				}

				if (newClass != null) {
					newCluster.getContents().add(newClass);
				}

				if (monitor.isCanceled()) {
					throw new InterruptedException();
				}
			}

			createBONClusterAndContentsNotationView(newCluster);
		}

		createLinksNotationView(bonST);

		monitor.subTask("Done.");
	}

	private void createLinksNotationView(BONST bonST) {

		Collection<ClientRelation> clientRelations = bonST.clientRelations;

		for (ClientRelation relation : clientRelations) {
			String relationName = relation.getSemanticLabel();

			GraphicalEditPart sourceEP = getClassEditPartByClassName(relation.client.name.getName());
			GraphicalEditPart targetEP = getClassEditPartByClassName(relation.supplier.name.getName());

			if (sourceEP == null || targetEP == null) {
				continue;
			}

			switch (relation.typeMark.mark) {
			case AGGREGATE:
				createAggregationLinkNotationView(sourceEP, targetEP);
				break;
			case SHAREDMARK:
				createAssociationLinkNotationView(sourceEP, targetEP);
				break;
			default:
				break;
			}
		}
	}

	private void createAssociationLinkNotationView(GraphicalEditPart sourceEP, GraphicalEditPart targetEP) {
		CreateConnectionViewAndElementRequest linkReq = new CreateConnectionViewAndElementRequest(
				BonideElementTypes.AssociationRel_4003,
				((IHintedType) BonideElementTypes.AssociationRel_4003).getSemanticHint(),
				modelEP.getDiagramPreferencesHint());

		ICommand createSubTopicsCmd = new DeferredCreateConnectionViewAndElementCommand(
				linkReq, sourceEP, targetEP, modelEP.getViewer());

		CompoundCommand compCmd = new CompoundCommand("Create Link");

		compCmd.add(new ICommandProxy(createSubTopicsCmd));
		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(compCmd);
	}

	private void createAggregationLinkNotationView(GraphicalEditPart sourceEP, GraphicalEditPart targetEP) {
		CreateConnectionViewAndElementRequest linkReq = new CreateConnectionViewAndElementRequest(
				BonideElementTypes.AggregationRel_4002,
				((IHintedType) BonideElementTypes.AggregationRel_4002).getSemanticHint(),
				modelEP.getDiagramPreferencesHint());

		ICommand createSubTopicsCmd = new DeferredCreateConnectionViewAndElementCommand(
				linkReq, sourceEP, targetEP, modelEP.getViewer());

		CompoundCommand compCmd = new CompoundCommand("Create Link");

		compCmd.add(new ICommandProxy(createSubTopicsCmd));
		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(compCmd);
	}

	public GraphicalEditPart getClassEditPartByClassName(String searchClassName) {
		return (findClassEditPart(modelEP, searchClassName));
	}

	private GraphicalEditPart findClassEditPart(AbstractEditPart searchEditPart, String searchClassName) {

		GraphicalEditPart foundEP = null;

		// don't recurse any further if there are no children, or if we've
		// gotten
		// down to the level of a class (since a class cannot contain other
		// classes)
		if (searchEditPart.getChildren().size() > 0 &&
				!(searchEditPart instanceof BONClassEditPart) &&
				!(searchEditPart instanceof BONClass2EditPart)) {

			Collection<AbstractEditPart> childElements = searchEditPart.getChildren();

			for (AbstractEditPart childEditPart : childElements) {
				foundEP = findClassEditPart(childEditPart, searchClassName);
				if (foundEP != null) {
					return (foundEP);
				}
			}
		}

		if (searchEditPart instanceof BONClassEditPart) {
			BONClassEditPart classEP = (BONClassEditPart) searchEditPart;
			BONClassNameEditPart classNameEP = (BONClassNameEditPart) classEP.getChildBySemanticHint(Integer.toString(BONClassNameEditPart.VISUAL_ID));

			String className = classNameEP.getEditText();
			if (className.trim().equals(searchClassName)) {
				return (classEP);
			}
		}
		
		if (searchEditPart instanceof BONClass2EditPart) {
			BONClass2EditPart classEP = (BONClass2EditPart) searchEditPart;
			BONClassName2EditPart classNameEP = (BONClassName2EditPart) classEP.getChildBySemanticHint(Integer.toString(BONClassName2EditPart.VISUAL_ID));

			String className = classNameEP.getEditText();
			if (className.trim().equals(searchClassName)) {
				return (classEP);
			}
		}

		return (null);
	}

	private void createBONClusterAndContentsNotationView(bonIDE.Cluster clusterModel) {

		CreateViewRequest.ViewDescriptor viewDescriptor = new CreateViewRequest.ViewDescriptor(
				new EObjectAdapter(clusterModel),
				org.eclipse.gmf.runtime.notation.Node.class,
				((IHintedType) BonideElementTypes.getElementType(ClusterEditPart.VISUAL_ID)).getSemanticHint(),
				true,
				modelEP.getDiagramPreferencesHint());

		viewDescriptor.setPersisted(true);

		CreateViewRequest createViewRequest = new CreateViewRequest(viewDescriptor);
		Command createViewCommand = modelEP.getCommand(createViewRequest);

		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(createViewCommand);

		// add the cluster to the model
		bonIDE.impl.ModelImpl modelImpl = (bonIDE.impl.ModelImpl) ((View) modelEP.getModel()).getElement();

		ArrayList<Abstraction> newAbstractionsList = new ArrayList<Abstraction>();
		Iterator<Abstraction> iter = modelImpl.getAbstractions().iterator();

		while (iter.hasNext()) {
			newAbstractionsList.add((Abstraction) iter.next());
		}

		newAbstractionsList.add(clusterModel);

		SetRequest reqSet = new SetRequest(
				modelEP.getEditingDomain(),
				(EObject) (((View) modelEP.getModel()).getElement()),
				BonIDEPackage.eINSTANCE.getModel_Abstractions(), newAbstractionsList);

		SetValueCommand operation = new SetValueCommand(reqSet);
		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(new ICommandProxy(operation));
	}

	private bonIDE.Cluster createBONClusterElement(Cluster ASTClusterNode) {

		ClusterImpl newCluster = (ClusterImpl) BonIDEFactoryImpl.eINSTANCE.createCluster();
		newCluster.setName(ASTClusterNode.getName());

		return (newCluster);
	}

	public BONClass createBONClassElement(Clazz ASTClassNode) {

		BONClassImpl newClass = (BONClassImpl) BonIDEFactoryImpl.eINSTANCE.createBONClass();
		newClass.setName(ASTClassNode.name.getName());

		ClassInterface ASTClassInterface = ASTClassNode.getClassInterface();

		if (ASTClassInterface == null) {
			return (null);
		}

		createBONClassIndexesElement(newClass, ASTClassInterface.indexing);
		createBONClassInheritanceElement(newClass, ASTClassInterface.parents);
		createBONClassFeaturesElement(newClass, ASTClassInterface.features);
		createBONClassInvariantsElement(newClass, ASTClassInterface.invariant);

		return (newClass);
	}

	private static void persistAllElements(View view) {

		if (view.getChildren().size() == 0) {
			ViewUtil.persistElement(view);
		} else {
			ViewUtil.persistElement(view);
			for (int index = view.getChildren().size() - 1; index > -1; index--) {
				persistAllElements((View) view.getChildren().get(index));
			}
		}
	}

	private void createBONClassInvariantsElement(BONClassImpl newClass, List<Expression> invariants) {

		if (invariants == null || invariants.size() == 0) {
			return;
		}

		ContractFormatter expFormatter = new ContractFormatter();
		Iterator<ie.ucd.bon.ast.Expression> invariantIter = invariants.iterator();

		while (invariantIter.hasNext()) {
			bonIDE.Invariant newInvariant = (bonIDE.Invariant) BonIDEFactoryImpl.eINSTANCE.createInvariant();

			ie.ucd.bon.ast.Expression invariant = invariantIter.next();
			PrettyPrintVisitor ppv = new PrettyPrintVisitor();
			invariant.accept(ppv);
			newInvariant.setContent(expFormatter.format(ppv.getVisitorOutputAsString()));
			newClass.getInvariants().add(newInvariant);
		}
	}

	private void createBONClassInheritanceElement(BONClassImpl newClass, List<Type> parents) {

		if (parents == null || parents.size() == 0) {
			return;
		}

		bonIDE.InheritanceClause inheritClause = (bonIDE.InheritanceClause) BonIDEFactoryImpl.eINSTANCE.createInheritanceClause();

		for (int parentIdx = 0; parentIdx < parents.size(); parentIdx++) {
			inheritClause.getParentNames().add(parents.get(parentIdx).getIdentifier());
		}

		newClass.setParents(inheritClause);
	}

	private void createBONClassIndexesElement(BONClassImpl newClass, Indexing indexing) {

		if (indexing == null || indexing.indexes.size() == 0) {
			return;
		}

		for (int indexIdx = 0; indexIdx < indexing.indexes.size(); indexIdx++) {

			ie.ucd.bon.ast.IndexClause indexClause = indexing.indexes.get(indexIdx);
			bonIDE.IndexClause idxClause = (bonIDE.IndexClause) BonIDEFactoryImpl.eINSTANCE.createIndexClause();
			idxClause.setIdentifier(indexClause.getId());

			for (int termIndex = 0; termIndex < indexClause.indexTerms.size(); termIndex++) {
				String termItem = indexClause.indexTerms.get(termIndex);

				if (termItem.startsWith("\"")) {
					termItem = termItem.substring(1);
				}

				if (termItem.endsWith("\"")) {
					termItem = termItem.substring(0, termItem.length() - 1);
				}

				idxClause.getTerms().add(termItem);
			}

			newClass.getIndexes().add(idxClause);
		}
	}

	private void createBONClassFeaturesElement(BONClassImpl newClass, List<Feature> features) {

		if (features == null || features.size() == 0) {
			return;
		}

		Iterator<ie.ucd.bon.ast.Feature> featIter = features.iterator();

		while (featIter.hasNext()) {
			ie.ucd.bon.ast.Feature currentFeat = featIter.next();

			Iterator<ie.ucd.bon.ast.FeatureSpecification> featSpecIter = currentFeat.featureSpecifications.iterator();

			while (featSpecIter.hasNext()) {
				bonIDE.Feature newFeature = (bonIDE.Feature) BonIDEFactoryImpl.eINSTANCE.createFeature();
				ie.ucd.bon.ast.FeatureSpecification featSpec = featSpecIter.next();

				// feature names
				Iterator<ie.ucd.bon.ast.FeatureName> featNameIter = featSpec.featureNames.iterator();

				while (featNameIter.hasNext()) {
					newFeature.getNames().add(featNameIter.next().getName());
				}

				// feature modifier
				newFeature.setModifier(getFeatureModifier(featSpec));

				// feature type (return value)
				if (featSpec.hasType != null) {
					newFeature.setType(getTypeDetail(featSpec.hasType.type));
				}

				// feature comment
				if (featSpec.getComment() != null) {
					newFeature.setComment(" -- " + featSpec.getComment());
				}

				// feature arguments
				Iterator<ie.ucd.bon.ast.FeatureArgument> featArgIter = featSpec.arguments.iterator();

				while (featArgIter.hasNext()) {
					bonIDE.FeatureArgument newArg = (bonIDE.FeatureArgument) BonIDEFactoryImpl.eINSTANCE
							.createFeatureArgument();
					ie.ucd.bon.ast.FeatureArgument featArg = featArgIter.next();

					newArg.setName(featArg.getIdentifier());
					newArg.setType(getTypeDetail(featArg.type));
					newFeature.getArguments().add(newArg);
				}

				// feature preConditions
				ContractFormatter expFormatter = new ContractFormatter();

				Iterator<ie.ucd.bon.ast.Expression> preCondIter = featSpec.getContracts().getPreconditions().iterator();

				while (preCondIter.hasNext()) {
					bonIDE.PreCondition newPreCond = (bonIDE.PreCondition) BonIDEFactoryImpl.eINSTANCE
							.createPreCondition();
					ie.ucd.bon.ast.Expression exp = preCondIter.next();
					PrettyPrintVisitor ppv = new PrettyPrintVisitor();
					exp.accept(ppv);
					newPreCond.setContent(expFormatter.format(ppv.getVisitorOutputAsString()));
					newFeature.getPreConditions().add(newPreCond);
				}

				// feature postConditions
				Iterator<ie.ucd.bon.ast.Expression> postCondIter = featSpec.getContracts().getPostconditions().iterator();

				while (postCondIter.hasNext()) {
					bonIDE.PostCondition newPostCond = (bonIDE.PostCondition) BonIDEFactoryImpl.eINSTANCE.createPostCondition();
					ie.ucd.bon.ast.Expression exp = postCondIter.next();
					PrettyPrintVisitor ppv = new PrettyPrintVisitor();
					exp.accept(ppv);
					newPostCond.setContent(expFormatter.format(ppv.getVisitorOutputAsString()));
					newFeature.getPostConditions().add(newPostCond);
				}

				newClass.getFeatures().add(newFeature);
			}
		}
	}

	private String getTypeDetail(ie.ucd.bon.ast.Type type) {

		if (type == null) {
			return ("");
		}

		if (type.actualGenerics.size() == 0) {
			return (type.identifier);
		} else {
			return (type.identifier + "[" + type.getActualGenerics().get(0).getIdentifier() + "]");
		}
	}

	private String getFeatureModifier(FeatureSpecification featSpec) {
		String modString;

		switch (featSpec.modifier) {
		case DEFERRED:
			modString = "*";
			break;
		case EFFECTIVE:
			modString = "\u207A";
			break;
		case REDEFINED:
			modString = "\u207A\u207A";
			break;
		case NONE:
		default:
			modString = "";
			break;
		}

		return (modString);
	}
};

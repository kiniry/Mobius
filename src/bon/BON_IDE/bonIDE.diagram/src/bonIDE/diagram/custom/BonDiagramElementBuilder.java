package bonIDE.diagram.custom;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
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

import bonIDE.Abstraction;
import bonIDE.BONClass;
import bonIDE.StaticAbstraction;
import bonIDE.diagram.edit.parts.BONClassEditPart;
import bonIDE.diagram.edit.parts.ModelEditPart;
import bonIDE.diagram.providers.BonideElementTypes;
import bonIDE.impl.BONClassImpl;
import bonIDE.impl.BonIDEFactoryImpl;
import bonIDE.impl.FeatureImpl;
import bonIDE.BonIDEPackage;

import ie.ucd.bon.API;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.FeatureSpecification.Modifier;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.PrettyPrintVisitor;

public class BonDiagramElementBuilder implements IRunnableWithProgress {

	private ModelEditPart modelEP;
	private String bonFileName;

	public BonDiagramElementBuilder(String fileName, ModelEditPart modelEditPart) {
		this.modelEP = modelEditPart;
		this.bonFileName = fileName;
	}

	public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {

		monitor.setTaskName("Building diagram...");
		monitor.subTask("Loading bon source file...");
		
		List<File> files = new ArrayList<File>();
		files.add(new File(bonFileName));
		ParsingTracker bonTracker = null;

		try {
			bonTracker = API.parse(files, false, false);
		} catch (Exception ex) {
			return;
		}

		monitor.subTask("Loading bon source file...done.");

		Collection<ParseResult> results = bonTracker.getParses();
		Iterator resultsIterator = results.iterator();
		ParseResult result = (ParseResult) resultsIterator.next();
		BonSourceFile bonSourceFile = result.getParse();

		for (int index = 0; index < bonSourceFile.bonSpecification.size(); index++) {
			AstNode node = bonSourceFile.bonSpecification.get(index);

			if (node instanceof ie.ucd.bon.ast.StaticDiagram) {

				for (int index2 = 0; index2 < ((StaticDiagram) node).components.size(); index2++) {
					AstNode node2 = ((StaticDiagram) node).components.get(index2);

					monitor.subTask("Creating class " + ((Clazz) node2).name.name + ".");

					if (node2 instanceof ie.ucd.bon.ast.Clazz) {
						createBONClassElement(modelEP, (Clazz) node2);
					}
				}
			}
		}
		monitor.subTask("Done.");
	}

	public static void createBONStaticDiagram(String fileName, ModelEditPart modelEP, Shell windowShell) {
		try {
			IRunnableWithProgress diagramBuildOperation = new BonDiagramElementBuilder(fileName, modelEP);
			new ProgressMonitorDialog(windowShell).run(true, true, diagramBuildOperation);
		} catch (InvocationTargetException e) {
			// handle exception
		} catch (InterruptedException e) {
			// handle cancelation
		}
	}

	public static void createBONClassElement(ModelEditPart modelEP, Clazz ASTClassNode) {

		BONClassImpl newClass = (BONClassImpl) BonIDEFactoryImpl.eINSTANCE.createBONClass();
		newClass.setName(ASTClassNode.name.getName());

		// --------------------------------------------------------------------------------------

		ClassInterface ASTClassInterface = ASTClassNode.getClassInterface();

		if (ASTClassInterface == null) {
			return;
		}

		createBONClassIndexesElement(newClass, ASTClassInterface.indexing);
		createBONClassInheritanceElement(newClass, ASTClassInterface.parents);
		createBONClassFeaturesElement(newClass, ASTClassInterface.features);

		// --------------------------------------------------------------------------------------

		/*
		 * FeatureImpl newFeature = (FeatureImpl)
		 * BonIDEFactoryImpl.eINSTANCE.createFeature();
		 * newFeature.setComment("-- this is a comment");
		 * newClass.getFeatures().add(newFeature);
		 */
		System.out.println("start making class " + System.currentTimeMillis());

		CreateViewRequest.ViewDescriptor viewDescriptor = new CreateViewRequest.ViewDescriptor(
				new EObjectAdapter(newClass),
				org.eclipse.gmf.runtime.notation.Node.class,
				((IHintedType) BonideElementTypes.getElementType(BONClassEditPart.VISUAL_ID)).getSemanticHint(),
				true,
				modelEP.getDiagramPreferencesHint());

		viewDescriptor.setPersisted(true);
		CreateViewRequest createViewRequest = new CreateViewRequest(viewDescriptor);
		Command createViewCommand = modelEP.getCommand(createViewRequest);

		System.out.println("end making class " + System.currentTimeMillis());
		System.out.println("start executing make class command" + System.currentTimeMillis());

		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(createViewCommand);

		System.out.println("end executing make class command" + System.currentTimeMillis());
		System.out.println("start adding class " + System.currentTimeMillis());
		// --------------------------------------------------------------------------------------

		bonIDE.impl.ModelImpl modelImpl = (bonIDE.impl.ModelImpl) ((View) modelEP.getModel()).getElement();

		ArrayList<Abstraction> newClasses = new ArrayList<Abstraction>();
		Iterator<Abstraction> iter = modelImpl.getAbstractions().iterator();

		while (iter.hasNext()) {
			newClasses.add((bonIDE.impl.AbstractionImpl) iter.next());
		}
		newClasses.add(newClass);

		SetRequest reqSet = new SetRequest(modelEP.getEditingDomain(), (EObject) (((View) modelEP.getModel())
				.getElement()),
				BonIDEPackage.eINSTANCE.getModel_Abstractions(), newClasses);

		SetValueCommand operation = new SetValueCommand(reqSet);
		modelEP.getDiagramEditDomain().getDiagramCommandStack().execute(new ICommandProxy(operation));

		System.out.println("end adding class " + System.currentTimeMillis());
	}

	private static void createBONClassInheritanceElement(BONClassImpl newClass, List<Type> parents) {
		if (parents == null || parents.size() == 0) {
			return;
		}

		bonIDE.InheritanceClause inheritClause = (bonIDE.InheritanceClause) BonIDEFactoryImpl.eINSTANCE
				.createInheritanceClause();

		for (int parentIdx = 0; parentIdx < parents.size(); parentIdx++) {
			inheritClause.getParentNames().add(parents.get(parentIdx).getIdentifier());
		}

		newClass.setParents(inheritClause);
	}

	private static void createBONClassIndexesElement(BONClassImpl newClass, Indexing indexing) {
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

	private static void createBONClassFeaturesElement(BONClassImpl newClass, List<Feature> features) {

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
				newFeature.setComment(featSpec.getComment());

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

	private static String getTypeDetail(ie.ucd.bon.ast.Type type) {

		if (type == null) {
			return ("");
		}

		if (type.actualGenerics.size() == 0) {
			return (type.identifier);
		} else {
			return (type.identifier + "[" + type.getActualGenerics().get(0).getIdentifier() + "]");
		}
	}

	private static String getFeatureModifier(FeatureSpecification featSpec) {
		String modString;

		switch (featSpec.modifier) {
		case DEFERRED:
			modString = "*";
			break;
		case EFFECTIVE:
			modString = "+";
			break;
		case REDEFINED:
			modString = "++";
			break;
		case NONE:
		default:
			modString = "";
			break;
		}

		return (modString);
	}
};

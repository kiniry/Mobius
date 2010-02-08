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
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;

public class BonDiagramElementBuilder implements IRunnableWithProgress {

	private ModelEditPart modelEP;
	private String bonFileName;

	public BonDiagramElementBuilder(String fileName, ModelEditPart modelEditPart) {
		this.modelEP = modelEditPart;
		this.bonFileName = fileName;
	}

	public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {

		monitor.setTaskName("Loading bon source file...");

		List<File> files = new ArrayList<File>();
		files.add(new File(bonFileName));
		ParsingTracker bonTracker = null;

		try {
			bonTracker = API.parse(files, false, false);
		} catch (Exception ex) {
			return;
		}

		monitor.setTaskName("Loading bon source file...done.");

		Collection<ParseResult> results = bonTracker.getParses();
		Iterator resultsIterator = results.iterator();
		ParseResult result = (ParseResult) resultsIterator.next();
		BonSourceFile bonSourceFile = result.getParse();

		for (int index = 0; index < bonSourceFile.bonSpecification.size(); index++) {
			AstNode node = bonSourceFile.bonSpecification.get(index);

			if (node instanceof ie.ucd.bon.ast.StaticDiagram) {

				for (int index2 = 0; index2 < ((StaticDiagram) node).components.size(); index2++) {
					AstNode node2 = ((StaticDiagram) node).components.get(index2);

					monitor.setTaskName("Creating class " + ((Clazz) node2).name.name + "...");

					if (node2 instanceof ie.ucd.bon.ast.Clazz) {
						createBONClassElement(modelEP, (Clazz) node2);
					}
				}
			}
		}
		monitor.setTaskName("Done.");
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

		// --------------------------------------------------------------------------------------

		FeatureImpl newFeature = (FeatureImpl) BonIDEFactoryImpl.eINSTANCE.createFeature();
		newFeature.setComment("-- this is a comment");
		newClass.getFeatures().add(newFeature);

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
		if (parents == null) {
			return;
		}
		
		bonIDE.InheritanceClause inheritClause = (bonIDE.InheritanceClause)BonIDEFactoryImpl.eINSTANCE.createInheritanceClause();
		
		for (int parentIndex = 0; parentIndex < parents.size(); parentIndex++) {
			inheritClause.getParentNames().add(parents.get(parentIndex).getIdentifier());			
		}
		
		newClass.setParents(inheritClause);
	}

	private static void createBONClassIndexesElement(BONClassImpl newClass, Indexing indexing) {

		if (indexing == null) {
			return;
		}
		for (int idxIndex = 0; idxIndex < indexing.indexes.size(); idxIndex++) {

			ie.ucd.bon.ast.IndexClause indexClause = indexing.indexes.get(idxIndex);
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
};

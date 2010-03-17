package bonIDE.diagram.providers;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.common.core.service.AbstractProvider;
import org.eclipse.gmf.runtime.common.core.service.IOperation;
import org.eclipse.gmf.runtime.common.ui.services.parser.GetParserOperation;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParser;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParserProvider;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserService;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.ui.services.parser.ParserHintAdapter;
import org.eclipse.gmf.runtime.notation.View;

/**
 * @generated
 */
public class BonideParserProvider extends AbstractProvider implements IParserProvider {

	/**
	 * @generated
	 */
	private IParser clusterName_5003Parser;

	/**
	 * @generated
	 */
	private IParser getClusterName_5003Parser() {
		if (clusterName_5003Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getCluster_Name()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			clusterName_5003Parser = parser;
		}
		return clusterName_5003Parser;
	}

	/**
	 * @generated
	 */
	private IParser bONClassName_5004Parser;

	/**
	 * @generated
	 */
	private IParser getBONClassName_5004Parser() {
		if (bONClassName_5004Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getBONClass_Name()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			bONClassName_5004Parser = parser;
		}
		return bONClassName_5004Parser;
	}

	/**
	 * @generated
	 */
	private IParser clusterName_5002Parser;

	/**
	 * @generated
	 */
	private IParser getClusterName_5002Parser() {
		if (clusterName_5002Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getCluster_Name()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			clusterName_5002Parser = parser;
		}
		return clusterName_5002Parser;
	}

	/**
	 * @generated
	 */
	private IParser bONClassName_5001Parser;

	/**
	 * @generated
	 */
	private IParser getBONClassName_5001Parser() {
		if (bONClassName_5001Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getBONClass_Name()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			bONClassName_5001Parser = parser;
		}
		return bONClassName_5001Parser;
	}

	/**
	 * @generated
	 */
	private IParser indexClauseIdentifier_5005Parser;

	/**
	 * @generated
	 */
	private IParser getIndexClauseIdentifier_5005Parser() {
		if (indexClauseIdentifier_5005Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getIndexClause_Identifier()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			indexClauseIdentifier_5005Parser = parser;
		}
		return indexClauseIdentifier_5005Parser;
	}

	/**
	 * @generated
	 */
	private IParser indexClauseTerms_5006Parser;

	/**
	 * @generated
	 */
	private IParser getIndexClauseTerms_5006Parser() {
		if (indexClauseTerms_5006Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getIndexClause_Terms()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			indexClauseTerms_5006Parser = parser;
		}
		return indexClauseTerms_5006Parser;
	}

	/**
	 * @generated
	 */
	private IParser inheritanceClauseParentNames_5010Parser;

	/**
	 * @generated
	 */
	private IParser getInheritanceClauseParentNames_5010Parser() {
		if (inheritanceClauseParentNames_5010Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getInheritanceClause_ParentNames()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			inheritanceClauseParentNames_5010Parser = parser;
		}
		return inheritanceClauseParentNames_5010Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureNames_5011Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureNames_5011Parser() {
		if (featureNames_5011Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeature_Names()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureNames_5011Parser = parser;
		}
		return featureNames_5011Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureModifier_5012Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureModifier_5012Parser() {
		if (featureModifier_5012Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeature_Modifier()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureModifier_5012Parser = parser;
		}
		return featureModifier_5012Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureType_5013Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureType_5013Parser() {
		if (featureType_5013Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeature_Type()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureType_5013Parser = parser;
		}
		return featureType_5013Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureComment_5014Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureComment_5014Parser() {
		if (featureComment_5014Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeature_Comment()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureComment_5014Parser = parser;
		}
		return featureComment_5014Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureArgumentName_5016Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureArgumentName_5016Parser() {
		if (featureArgumentName_5016Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeatureArgument_Name()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureArgumentName_5016Parser = parser;
		}
		return featureArgumentName_5016Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureArgumentContainerType_5017Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureArgumentContainerType_5017Parser() {
		if (featureArgumentContainerType_5017Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeatureArgument_ContainerType()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureArgumentContainerType_5017Parser = parser;
		}
		return featureArgumentContainerType_5017Parser;
	}

	/**
	 * @generated
	 */
	private IParser featureArgumentType_5018Parser;

	/**
	 * @generated
	 */
	private IParser getFeatureArgumentType_5018Parser() {
		if (featureArgumentType_5018Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getFeatureArgument_Type()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			featureArgumentType_5018Parser = parser;
		}
		return featureArgumentType_5018Parser;
	}

	/**
	 * @generated
	 */
	private IParser preCondition_3008Parser;

	/**
	 * @generated
	 */
	private IParser getPreCondition_3008Parser() {
		if (preCondition_3008Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getPreCondition_Content()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			preCondition_3008Parser = parser;
		}
		return preCondition_3008Parser;
	}

	/**
	 * @generated
	 */
	private IParser postCondition_3009Parser;

	/**
	 * @generated
	 */
	private IParser getPostCondition_3009Parser() {
		if (postCondition_3009Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getPostCondition_Content()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			postCondition_3009Parser = parser;
		}
		return postCondition_3009Parser;
	}

	/**
	 * @generated
	 */
	private IParser invariantContent_5019Parser;

	/**
	 * @generated
	 */
	private IParser getInvariantContent_5019Parser() {
		if (invariantContent_5019Parser == null) {
			EAttribute[] features = new EAttribute[] {
					bonIDE.BonIDEPackage.eINSTANCE.getInvariant_Content()
					};
			bonIDE.diagram.parsers.MessageFormatParser parser = new bonIDE.diagram.parsers.MessageFormatParser(features);
			invariantContent_5019Parser = parser;
		}
		return invariantContent_5019Parser;
	}

	/**
	 * @generated
	 */
	protected IParser getParser(int visualID) {
		switch (visualID) {
		case bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID:
			return getClusterName_5003Parser();
		case bonIDE.diagram.edit.parts.BONClassNameEditPart.VISUAL_ID:
			return getBONClassName_5004Parser();
		case bonIDE.diagram.edit.parts.ClusterName2EditPart.VISUAL_ID:
			return getClusterName_5002Parser();
		case bonIDE.diagram.edit.parts.BONClassName2EditPart.VISUAL_ID:
			return getBONClassName_5001Parser();
		case bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart.VISUAL_ID:
			return getIndexClauseIdentifier_5005Parser();
		case bonIDE.diagram.edit.parts.IndexClauseTermsEditPart.VISUAL_ID:
			return getIndexClauseTerms_5006Parser();
		case bonIDE.diagram.edit.parts.InheritanceClauseParentNamesEditPart.VISUAL_ID:
			return getInheritanceClauseParentNames_5010Parser();
		case bonIDE.diagram.edit.parts.FeatureNamesEditPart.VISUAL_ID:
			return getFeatureNames_5011Parser();
		case bonIDE.diagram.edit.parts.FeatureModifierEditPart.VISUAL_ID:
			return getFeatureModifier_5012Parser();
		case bonIDE.diagram.edit.parts.FeatureTypeEditPart.VISUAL_ID:
			return getFeatureType_5013Parser();
		case bonIDE.diagram.edit.parts.FeatureCommentEditPart.VISUAL_ID:
			return getFeatureComment_5014Parser();
		case bonIDE.diagram.edit.parts.FeatureArgumentNameEditPart.VISUAL_ID:
			return getFeatureArgumentName_5016Parser();
		case bonIDE.diagram.edit.parts.FeatureArgumentContainerTypeEditPart.VISUAL_ID:
			return getFeatureArgumentContainerType_5017Parser();
		case bonIDE.diagram.edit.parts.FeatureArgumentTypeEditPart.VISUAL_ID:
			return getFeatureArgumentType_5018Parser();
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getPreCondition_3008Parser();
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getPostCondition_3009Parser();
		case bonIDE.diagram.edit.parts.InvariantContentEditPart.VISUAL_ID:
			return getInvariantContent_5019Parser();
		}
		return null;
	}

	/**
	 * Utility method that consults ParserService
	 * @generated
	 */
	public static IParser getParser(IElementType type, EObject object, String parserHint) {
		return ParserService.getInstance().getParser(new HintAdapter(type, object, parserHint));
	}

	/**
	 * @generated
	 */
	public IParser getParser(
			IAdaptable hint) {
		String vid = (String) hint.getAdapter(String.class);
		if (vid != null) {
			return getParser(bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(vid));
		}
		View view =
				(View) hint.getAdapter(View.class);
		if (view != null) {
			return getParser(bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view));
		}
		return null;
	}

	/**
	 * @generated
	 */
	public boolean provides(IOperation operation) {
		if (operation instanceof GetParserOperation) {
			IAdaptable hint =
					((GetParserOperation) operation).getHint();
			if (bonIDE.diagram.providers.BonideElementTypes.getElement(hint) == null) {
				return false;
			}
			return getParser(hint) != null;
		}
		return false;
	}

	/**
	 * @generated
	 */
	private static class HintAdapter extends ParserHintAdapter {

		/**
		 * @generated
		 */
		private final IElementType elementType;

		/**
		 * @generated
		 */
		public HintAdapter(IElementType type, EObject object, String parserHint) {
			super(object, parserHint);
			assert type != null;
			elementType = type;
		}

		/**
		 * @generated
		 */
		public Object getAdapter(Class adapter) {
			if (IElementType.class.equals(adapter)) {
				return elementType;
			}
			return super.getAdapter(adapter);
		}
	}

}

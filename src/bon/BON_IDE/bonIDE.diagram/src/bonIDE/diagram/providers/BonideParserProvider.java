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

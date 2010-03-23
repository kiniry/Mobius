package bonIDE.diagram.navigator;

import org.eclipse.gmf.runtime.common.ui.services.parser.CommonParserHint;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParser;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserOptions;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.jface.viewers.ITreePathLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.ViewerLabel;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonLabelProvider;

/**
 * @generated
 */
public class BonideNavigatorLabelProvider extends LabelProvider implements ICommonLabelProvider, ITreePathLabelProvider {

	/**
	 * @generated
	 */
	static {
		bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getImageRegistry().put(
				"Navigator?UnknownElement", ImageDescriptor.getMissingImageDescriptor()); //$NON-NLS-1$
		bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getImageRegistry().put(
				"Navigator?ImageNotFound", ImageDescriptor.getMissingImageDescriptor()); //$NON-NLS-1$
	}

	/**
	 * @generated
	 */
	public void updateLabel(ViewerLabel label, TreePath elementPath) {
		Object element = elementPath.getLastSegment();
		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorItem
				&& !isOwnView(((bonIDE.diagram.navigator.BonideNavigatorItem) element).getView())) {
			return;
		}
		label.setText(getText(element));
		label.setImage(getImage(element));
	}

	/**
	 * @generated
	 */
	public Image getImage(Object element) {
		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorGroup) {
			bonIDE.diagram.navigator.BonideNavigatorGroup group = (bonIDE.diagram.navigator.BonideNavigatorGroup) element;
			return bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getBundledImage(group.getIcon());
		}

		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorItem) {
			bonIDE.diagram.navigator.BonideNavigatorItem navigatorItem = (bonIDE.diagram.navigator.BonideNavigatorItem) element;
			if (!isOwnView(navigatorItem.getView())) {
				return super.getImage(element);
			}
			return getImage(navigatorItem.getView());
		}

		return super.getImage(element);
	}

	/**
	 * @generated
	 */
	public Image getImage(View view) {
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			return getImage("Navigator?Diagram?http://www.ucd.ie/bonIDE?Model", bonIDE.diagram.providers.BonideElementTypes.Model_1000); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getImage(
					"Navigator?TopLevelNode?http://www.ucd.ie/bonIDE?Cluster", bonIDE.diagram.providers.BonideElementTypes.Cluster_2001); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getImage(
					"Navigator?TopLevelNode?http://www.ucd.ie/bonIDE?BONClass", bonIDE.diagram.providers.BonideElementTypes.BONClass_2002); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getImage("Navigator?Node?http://www.ucd.ie/bonIDE?Cluster", bonIDE.diagram.providers.BonideElementTypes.Cluster_3001); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getImage("Navigator?Node?http://www.ucd.ie/bonIDE?BONClass", bonIDE.diagram.providers.BonideElementTypes.BONClass_3002); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?IndexClause", bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?InheritanceClause", bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return getImage("Navigator?Node?http://www.ucd.ie/bonIDE?Feature", bonIDE.diagram.providers.BonideElementTypes.Feature_3006); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?FeatureArgument", bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?PreCondition", bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?PostCondition", bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return getImage("Navigator?Node?http://www.ucd.ie/bonIDE?Invariant", bonIDE.diagram.providers.BonideElementTypes.Invariant_3010); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Link?http://www.ucd.ie/bonIDE?InheritanceRel", bonIDE.diagram.providers.BonideElementTypes.InheritanceRel_4001); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Link?http://www.ucd.ie/bonIDE?AggregationRel", bonIDE.diagram.providers.BonideElementTypes.AggregationRel_4002); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getImage(
					"Navigator?Link?http://www.ucd.ie/bonIDE?AssociationRel", bonIDE.diagram.providers.BonideElementTypes.AssociationRel_4003); //$NON-NLS-1$
		}
		return getImage("Navigator?UnknownElement", null); //$NON-NLS-1$
	}

	/**
	 * @generated
	 */
	private Image getImage(String key, IElementType elementType) {
		ImageRegistry imageRegistry = bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getImageRegistry();
		Image image = imageRegistry.get(key);
		if (image == null && elementType != null && bonIDE.diagram.providers.BonideElementTypes.isKnownElementType(elementType)) {
			image = bonIDE.diagram.providers.BonideElementTypes.getImage(elementType);
			imageRegistry.put(key, image);
		}

		if (image == null) {
			image = imageRegistry.get("Navigator?ImageNotFound"); //$NON-NLS-1$
			imageRegistry.put(key, image);
		}
		return image;
	}

	/**
	 * @generated
	 */
	public String getText(Object element) {
		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorGroup) {
			bonIDE.diagram.navigator.BonideNavigatorGroup group = (bonIDE.diagram.navigator.BonideNavigatorGroup) element;
			return group.getGroupName();
		}

		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorItem) {
			bonIDE.diagram.navigator.BonideNavigatorItem navigatorItem = (bonIDE.diagram.navigator.BonideNavigatorItem) element;
			if (!isOwnView(navigatorItem.getView())) {
				return null;
			}
			return getText(navigatorItem.getView());
		}

		return super.getText(element);
	}

	/**
	 * @generated
	 */
	public String getText(View view) {
		if (view.getElement() != null && view.getElement().eIsProxy()) {
			return getUnresolvedDomainElementProxyText(view);
		}
		switch (bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(view)) {
		case bonIDE.diagram.edit.parts.ModelEditPart.VISUAL_ID:
			return getModel_1000Text(view);
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getCluster_2001Text(view);
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getBONClass_2002Text(view);
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getCluster_3001Text(view);
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getBONClass_3002Text(view);
		case bonIDE.diagram.edit.parts.IndexClauseEditPart.VISUAL_ID:
			return getIndexClause_3003Text(view);
		case bonIDE.diagram.edit.parts.InheritanceClauseEditPart.VISUAL_ID:
			return getInheritanceClause_3005Text(view);
		case bonIDE.diagram.edit.parts.FeatureEditPart.VISUAL_ID:
			return getFeature_3006Text(view);
		case bonIDE.diagram.edit.parts.FeatureArgumentEditPart.VISUAL_ID:
			return getFeatureArgument_3007Text(view);
		case bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID:
			return getPreCondition_3008Text(view);
		case bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID:
			return getPostCondition_3009Text(view);
		case bonIDE.diagram.edit.parts.InvariantEditPart.VISUAL_ID:
			return getInvariant_3010Text(view);
		case bonIDE.diagram.edit.parts.InheritanceRelEditPart.VISUAL_ID:
			return getInheritanceRel_4001Text(view);
		case bonIDE.diagram.edit.parts.AggregationRelEditPart.VISUAL_ID:
			return getAggregationRel_4002Text(view);
		case bonIDE.diagram.edit.parts.AssociationRelEditPart.VISUAL_ID:
			return getAssociationRel_4003Text(view);
		}
		return getUnknownElementText(view);
	}

	/**
	 * @generated
	 */
	private String getModel_1000Text(View view) {
		return ""; //$NON-NLS-1$
	}

	/**
	 * @generated
	 */
	private String getCluster_2001Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(bonIDE.diagram.providers.BonideElementTypes.Cluster_2001,
				view.getElement() != null ? view.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5003); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getBONClass_2002Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(bonIDE.diagram.providers.BonideElementTypes.BONClass_2002,
				view.getElement() != null ? view.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.BONClassNameEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5004); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getCluster_3001Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(bonIDE.diagram.providers.BonideElementTypes.Cluster_3001,
				view.getElement() != null ? view.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.ClusterName2EditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5002); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getBONClass_3002Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(bonIDE.diagram.providers.BonideElementTypes.BONClass_3002,
				view.getElement() != null ? view.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.BONClassName2EditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5001); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getIndexClause_3003Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.IndexClause_3003, view.getElement() != null ? view.getElement() : view,
				bonIDE.diagram.part.BonideVisualIDRegistry.getType(bonIDE.diagram.edit.parts.IndexClauseIdentifierEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5005); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getInheritanceClause_3005Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.InheritanceClause_3005, view.getElement() != null ? view.getElement() : view,
				CommonParserHint.DESCRIPTION);
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5009); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getFeature_3006Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(bonIDE.diagram.providers.BonideElementTypes.Feature_3006,
				view.getElement() != null ? view.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.FeatureNamesEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5011); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getFeatureArgument_3007Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.FeatureArgument_3007, view.getElement() != null ? view.getElement() : view,
				CommonParserHint.DESCRIPTION);
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5015); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getPreCondition_3008Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.PreCondition_3008, view.getElement() != null ? view.getElement() : view,
				bonIDE.diagram.part.BonideVisualIDRegistry.getType(bonIDE.diagram.edit.parts.PreConditionEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 3008); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getPostCondition_3009Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.PostCondition_3009, view.getElement() != null ? view.getElement() : view,
				bonIDE.diagram.part.BonideVisualIDRegistry.getType(bonIDE.diagram.edit.parts.PostConditionEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 3009); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getInvariant_3010Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.Invariant_3010, view.getElement() != null ? view.getElement() : view,
				bonIDE.diagram.part.BonideVisualIDRegistry.getType(bonIDE.diagram.edit.parts.InvariantContentEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view), ParserOptions.NONE
					.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("Parser was not found for label " + 5019); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getInheritanceRel_4001Text(View view) {
		bonIDE.InheritanceRel domainModelElement = (bonIDE.InheritanceRel) view.getElement();
		if (domainModelElement != null) {
			return String.valueOf(domainModelElement.getType());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("No domain element for view with visualID = " + 4001); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getAggregationRel_4002Text(View view) {
		bonIDE.AggregationRel domainModelElement = (bonIDE.AggregationRel) view.getElement();
		if (domainModelElement != null) {
			return domainModelElement.getName();
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("No domain element for view with visualID = " + 4002); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getAssociationRel_4003Text(View view) {
		bonIDE.AssociationRel domainModelElement = (bonIDE.AssociationRel) view.getElement();
		if (domainModelElement != null) {
			return domainModelElement.getName();
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError("No domain element for view with visualID = " + 4003); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getUnknownElementText(View view) {
		return "<UnknownElement Visual_ID = " + view.getType() + ">"; //$NON-NLS-1$  //$NON-NLS-2$
	}

	/**
	 * @generated
	 */
	private String getUnresolvedDomainElementProxyText(View view) {
		return "<Unresolved domain element Visual_ID = " + view.getType() + ">"; //$NON-NLS-1$  //$NON-NLS-2$
	}

	/**
	 * @generated
	 */
	public void init(ICommonContentExtensionSite aConfig) {
	}

	/**
	 * @generated
	 */
	public void restoreState(IMemento aMemento) {
	}

	/**
	 * @generated
	 */
	public void saveState(IMemento aMemento) {
	}

	/**
	 * @generated
	 */
	public String getDescription(Object anElement) {
		return null;
	}

	/**
	 * @generated
	 */
	private boolean isOwnView(View view) {
		return bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(bonIDE.diagram.part.BonideVisualIDRegistry.getModelID(view));
	}

}

package bonIDE.diagram.navigator;

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
			return getImage(
					"Navigator?Diagram?http://www.ucd.ie/bonIDE?Model", bonIDE.diagram.providers.BonideElementTypes.Model_1000); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.ClusterEditPart.VISUAL_ID:
			return getImage(
					"Navigator?TopLevelNode?http://www.ucd.ie/bonIDE?Cluster", bonIDE.diagram.providers.BonideElementTypes.Cluster_2001); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.BONClassEditPart.VISUAL_ID:
			return getImage(
					"Navigator?TopLevelNode?http://www.ucd.ie/bonIDE?BONClass", bonIDE.diagram.providers.BonideElementTypes.BONClass_2002); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.Cluster2EditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?Cluster", bonIDE.diagram.providers.BonideElementTypes.Cluster_3001); //$NON-NLS-1$
		case bonIDE.diagram.edit.parts.BONClass2EditPart.VISUAL_ID:
			return getImage(
					"Navigator?Node?http://www.ucd.ie/bonIDE?BONClass", bonIDE.diagram.providers.BonideElementTypes.BONClass_3002); //$NON-NLS-1$
		}
		return getImage("Navigator?UnknownElement", null); //$NON-NLS-1$
	}

	/**
	 * @generated
	 */
	private Image getImage(String key, IElementType elementType) {
		ImageRegistry imageRegistry = bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getImageRegistry();
		Image image = imageRegistry.get(key);
		if (image == null && elementType != null
				&& bonIDE.diagram.providers.BonideElementTypes.isKnownElementType(elementType)) {
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
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.Cluster_2001, view.getElement() != null ? view.getElement()
						: view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.ClusterNameEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view),
					ParserOptions.NONE.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError(
					"Parser was not found for label " + 5003); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getBONClass_2002Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.BONClass_2002, view.getElement() != null ? view
						.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.BONClassNameEditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view),
					ParserOptions.NONE.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError(
					"Parser was not found for label " + 5004); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getCluster_3001Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.Cluster_3001, view.getElement() != null ? view.getElement()
						: view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.ClusterName2EditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view),
					ParserOptions.NONE.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError(
					"Parser was not found for label " + 5002); //$NON-NLS-1$
			return ""; //$NON-NLS-1$
		}
	}

	/**
	 * @generated
	 */
	private String getBONClass_3002Text(View view) {
		IParser parser = bonIDE.diagram.providers.BonideParserProvider.getParser(
				bonIDE.diagram.providers.BonideElementTypes.BONClass_3002, view.getElement() != null ? view
						.getElement() : view, bonIDE.diagram.part.BonideVisualIDRegistry
						.getType(bonIDE.diagram.edit.parts.BONClassName2EditPart.VISUAL_ID));
		if (parser != null) {
			return parser.getPrintString(new EObjectAdapter(view.getElement() != null ? view.getElement() : view),
					ParserOptions.NONE.intValue());
		} else {
			bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().logError(
					"Parser was not found for label " + 5001); //$NON-NLS-1$
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
		return bonIDE.diagram.edit.parts.ModelEditPart.MODEL_ID.equals(bonIDE.diagram.part.BonideVisualIDRegistry
				.getModelID(view));
	}

}

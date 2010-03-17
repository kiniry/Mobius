package bonIDE.diagram.navigator;

import org.eclipse.jface.viewers.ViewerSorter;

/**
 * @generated
 */
public class BonideNavigatorSorter extends ViewerSorter {

	/**
	 * @generated
	 */
	private static final int GROUP_CATEGORY = 7015;

	/**
	 * @generated
	 */
	public int category(Object element) {
		if (element instanceof bonIDE.diagram.navigator.BonideNavigatorItem) {
			bonIDE.diagram.navigator.BonideNavigatorItem item = (bonIDE.diagram.navigator.BonideNavigatorItem) element;
			return bonIDE.diagram.part.BonideVisualIDRegistry.getVisualID(item.getView());
		}
		return GROUP_CATEGORY;
	}

}

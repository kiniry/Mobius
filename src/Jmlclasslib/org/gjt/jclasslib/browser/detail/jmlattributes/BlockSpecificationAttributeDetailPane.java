/*
 * Created on May 26, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package org.gjt.jclasslib.browser.detail.jmlattributes;

import org.gjt.jclasslib.browser.BrowserServices;
import org.gjt.jclasslib.browser.detail.attributes.AbstractAttributeListDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.AbstractAttributeTableModel;
import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.jmlattributes.BlockSpec;
import org.gjt.jclasslib.structures.jmlattributes.BlockSpecificationAttribute;

/**
 *
 *  @author L. Burdy
 **/
public class BlockSpecificationAttributeDetailPane
	extends AbstractAttributeListDetailPane /*FixedListDetailPane*/ {

	/**
		 Constructor.
		 @param services the associated browser services.
	  */
	public BlockSpecificationAttributeDetailPane(BrowserServices services) {
		super(services);
	}

	protected AbstractAttributeTableModel createTableModel(AttributeInfo attribute) {
		return new AttributeTableModel(attribute);
	}

	private class AttributeTableModel extends AbstractAttributeTableModel {

		private static final int COLUMN_COUNT = BASE_COLUMN_COUNT + 1;

		private BlockSpec[] blockSpec;

		private AttributeTableModel(AttributeInfo attribute) {
			super(attribute);
			blockSpec = ((BlockSpecificationAttribute) attribute).getSpec();
		}

		public int getColumnWidth(int column) {
			return VERBOSE_COLUMN_WIDTH;
		}

		public int getRowCount() {
			return blockSpec.length * 5;
		}

		public int getColumnCount() {
			return COLUMN_COUNT;
		}

		protected String doGetColumnName(int column) {
			return "";
		}

		protected Class doGetColumnClass(int column) {
			return String.class;
		}

		protected Object doGetValueAt(int row, int column) {

			BlockSpec spec = blockSpec[row / 5];

			switch (row % 5) {
				case 0 :
					return spec.getStartIndex();
				case 1 :
					return spec.getEndIndex();
				case 2 :
					return spec.getRequires();
				case 3 :
					return spec.getModifies();
				case 4 :
					return spec.getEnsures();
				default :
					return "";
			}
		}
	}

	//	// Visual components
	//
	//	private ExtendedJLabel lblAssert;
	//
	//	/**
	//		Constructor.
	//		@param services the associated browser services.
	//	 */
	//	public BlockSpecificationAttributeDetailPane(BrowserServices services) {
	//		super(services);
	//	}
	//
	//	protected void setupLabels() {
	//		addDetailPaneEntry(
	//			normalLabel("block:"),
	//			null,
	//			lblAssert = highlightLabel());
	//	}
	//
	//	public void show(TreePath treePath) {
	//		BlockSpecificationAttribute attribute =
	//			(BlockSpecificationAttribute) findAttribute(treePath);
	//
	//		lblAssert.setText(attribute.getBlockSpecText());
	//
	//	}

}

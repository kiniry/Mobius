/*
 * Created on May 26, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package org.gjt.jclasslib.browser.detail.jmlattributes;

import org.gjt.jclasslib.browser.BrowserServices;
import org
	.gjt
	.jclasslib
	.browser
	.detail
	.attributes
	.AbstractAttributeListDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.AbstractAttributeTableModel;
import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.jmlattributes.BlockSpec;
import org.gjt.jclasslib.structures.jmlattributes.Formula;
import org.gjt.jclasslib.structures.jmlattributes.MethodSpec;
import org.gjt.jclasslib.structures.jmlattributes.MethodSpecificationAttribute;

/**
 *
 *  @author L. Burdy
 **/
public class MethodSpecificationAttributeDetailPane
	extends AbstractAttributeListDetailPane {

	public MethodSpecificationAttributeDetailPane(BrowserServices services) {
		super(services);
	}

	protected AbstractAttributeTableModel createTableModel(AttributeInfo attribute) {
		return new AttributeTableModel(attribute);
	}

	private class AttributeTableModel extends AbstractAttributeTableModel {

		private static final int COLUMN_COUNT = BASE_COLUMN_COUNT + 1;

		private Formula requires;
		private MethodSpec[] methodSpec;

		private AttributeTableModel(AttributeInfo attribute) {
			super(attribute);
			requires = ((MethodSpecificationAttribute) attribute).getRequires();
			methodSpec = ((MethodSpecificationAttribute) attribute).getSpec();
		}

		public int getColumnWidth(int column) {
			return VERBOSE_COLUMN_WIDTH;
		}

		public int getRowCount() {
			return 3 + methodSpec.length * 4 + methodSpec.length - 1;
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

			if (row == 0)
				return "requires " + requires;
			else if (row == 1)
				return "{|";
			else
				switch ((row - 2) % 5) {
					case 0 :
						return methodSpec[(row - 2) / 5].getRequires();
					case 1 :
						return methodSpec[(row - 2) / 5].getModifies();
					case 2 :
						return methodSpec[(row - 2) / 5].getEnsures();
					case 3 :
						return methodSpec[(row - 2) / 5].getExsures();
					case 4 :
						if (row == getRowCount() - 1)
							return "|}";
						else
							return "also";
					default :
						return "";
				}
		}
	}
	//	// Visual components
	//    
	//	private ExtendedJLabel lblRequires;
	//	private ExtendedJLabel lblSpec;
	//    
	//	/**
	//		Constructor.
	//		@param services the associated browser services.
	//	 */
	//	public MethodSpecificationAttributeDetailPane(BrowserServices services) {
	//		super(services);
	//	}
	//    
	//	protected void setupLabels() {
	//		addDetailPaneEntry(normalLabel("requires:"),
	//						   null,
	//						   lblRequires = highlightLabel());
	//		addDetailPaneEntry(normalLabel("spec cases:"),
	//						   null,
	//						   lblSpec = highlightLabel());
	//	}
	//
	//	public void show(TreePath treePath) {
	//        
	//		MethodSpecificationAttribute attribute = (MethodSpecificationAttribute)findAttribute(treePath);
	//
	//		lblRequires.setText(attribute.getRequires().toString());
	//		lblSpec.setText(attribute.getSpecText());
	//
	////		constantPoolHyperlink(lblSourceFile,
	////							  lblSourceFileVerbose,
	////							  attribute.getSourcefileIndex());
	//        
	////		super.show(treePath);
	//	}

}

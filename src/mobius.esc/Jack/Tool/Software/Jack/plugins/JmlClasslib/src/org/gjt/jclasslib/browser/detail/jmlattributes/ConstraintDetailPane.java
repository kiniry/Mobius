/*
 * Created on May 26, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package org.gjt.jclasslib.browser.detail.jmlattributes;

import javax.swing.tree.TreePath;

import org.gjt.jclasslib.browser.BrowserServices;
import org.gjt.jclasslib.browser.detail.FixedListDetailPane;
import org.gjt.jclasslib.structures.jmlattributes.ConstraintAttribute;
import org.gjt.jclasslib.util.ExtendedJLabel;

/**
 *
 *  @author L. Burdy
 **/
public class ConstraintDetailPane extends FixedListDetailPane {

	// Visual components

	private ExtendedJLabel lblAssert;

	/**
		Constructor.
		@param services the associated browser services.
	 */
	public ConstraintDetailPane(BrowserServices services) {
		super(services);
	}

	protected void setupLabels() {
		addDetailPaneEntry(
			normalLabel("constraint:"),
			null,
			lblAssert = highlightLabel());
	}

	public void show(TreePath treePath) {

		ConstraintAttribute attribute =
			(ConstraintAttribute) findAttribute(treePath);

		lblAssert.setText(attribute.getConstraintText());

	}

}

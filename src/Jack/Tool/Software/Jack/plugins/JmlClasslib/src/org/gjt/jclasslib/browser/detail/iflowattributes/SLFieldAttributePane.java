/*
 * Created on January 19, 2005
 *
 */
package org.gjt.jclasslib.browser.detail.iflowattributes;

import javax.swing.tree.TreePath;

import org.gjt.jclasslib.browser.BrowserServices;
import org.gjt.jclasslib.browser.detail.FixedListDetailPane;
import org.gjt.jclasslib.structures.iflowattributes.SecLevelFieldAttribute;
import org.gjt.jclasslib.structures.iflowattributes.Util;
import org.gjt.jclasslib.util.ExtendedJLabel;


/**
 *
 *  @author L. Burdy, Luca Martini
 **/
public class SLFieldAttributePane extends FixedListDetailPane {

	// Visual components
    
	private ExtendedJLabel lblSLField;
    
	/**
		Constructor.
		@param services the associated browser services.
	 */
	public SLFieldAttributePane(BrowserServices services) {
		super(services);
	}
    
	protected void setupLabels() {
		addDetailPaneEntry(normalLabel("Field Security level:"),
						   null,
						   lblSLField = highlightLabel());
	}

	public void show(TreePath treePath) {
        
		SecLevelFieldAttribute attribute = (SecLevelFieldAttribute)findAttribute(treePath);

		lblSLField.setText(Util.secLeveByte2String(attribute.level));

	}
    

}

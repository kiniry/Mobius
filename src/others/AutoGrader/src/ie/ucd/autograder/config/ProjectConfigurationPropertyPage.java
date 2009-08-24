package ie.ucd.autograder.config;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.dialogs.PropertyPage;

public class ProjectConfigurationPropertyPage extends PropertyPage {

  private GradeBoundariesComposite boundaries;
  
	public ProjectConfigurationPropertyPage() {
		super();
	}

	protected Control createContents(Composite parent) {
		
		TabFolder tab = new TabFolder(parent, SWT.BORDER);
		TabItem tab1 = new TabItem(tab, SWT.NULL);
		tab1.setText("Grade boundaries");
		TabItem tab2 = new TabItem(tab, SWT.NULL);
		tab2.setText("Graders");
		
		boundaries = new GradeBoundariesComposite(tab);
		tab1.setControl(boundaries);
		
		Composite tab2contents = new Composite(tab, SWT.NONE);
		tab2.setControl(tab2contents);
		
		return tab;
	}
	
	public boolean performOk() {
		boolean boundariesOk = boundaries.performOk();
	  //TODO validate and store the values in the page's fields.
		
		return true;
	}

	
	
}
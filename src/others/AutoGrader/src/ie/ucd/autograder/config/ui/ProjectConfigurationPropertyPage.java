package ie.ucd.autograder.config.ui;

import ie.ucd.autograder.config.AGConfig;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.dialogs.PropertyPage;

public class ProjectConfigurationPropertyPage extends PropertyPage {

  private GradeBoundariesComposite boundaries;
  private GradersComposite graders;

  public ProjectConfigurationPropertyPage() {
    super();
  }

  protected Control createContents(Composite parent) {

    TabFolder tab = new TabFolder(parent, SWT.BORDER);
    TabItem tab1 = new TabItem(tab, SWT.NULL);
    tab1.setText("Grade boundaries");
    TabItem tab2 = new TabItem(tab, SWT.NULL);
    tab2.setText("Graders");

    boundaries = new GradeBoundariesComposite(tab, this);
    if (getPreferenceStore() != null){
      boundaries.setPreferenceStore(getPreferenceStore());
    }
    tab1.setControl(boundaries);

    graders = new GradersComposite(tab, this);
    if (getPreferenceStore() != null) {
      graders.setPreferenceStore(getPreferenceStore());
    }
    tab2.setControl(graders);

    return tab;
  }

  public boolean performOk() {
    if (!boundaries.performOk() || !graders.performOk()) {
      return false;
    } else {
      return true;
    }
  }

  @Override
  public void setElement(IAdaptable element) {
    super.setElement(element);
    setupPreferenceStore(element);
  }

  private void setupPreferenceStore(IAdaptable element) {

    IProject project = null;

    if (element instanceof IResource) {
      final IResource resource = (IResource)element;
      project = resource.getProject();
    } else if (element instanceof IJavaProject) {
      final IJavaProject jProject = (IJavaProject)element;
      project = jProject.getProject();
    }

    if (project != null) {
      IPreferenceStore store = AGConfig.getPreferenceStoreForProject(project);
      setPreferenceStore(store);
    }
  }

  @Override
  public void setPreferenceStore(IPreferenceStore store) {
     super.setPreferenceStore(store);
     if (boundaries != null) {
       boundaries.setPreferenceStore(store);
     }
  }

}
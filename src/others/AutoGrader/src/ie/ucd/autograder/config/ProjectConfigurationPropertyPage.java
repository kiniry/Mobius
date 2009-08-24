package ie.ucd.autograder.config;

import ie.ucd.autograder.AutoGraderPlugin;
import ie.ucd.autograder.grading.Grade;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.dialogs.PropertyPage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

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

    boundaries = new GradeBoundariesComposite(tab, this);
    if (getPreferenceStore() != null){
      boundaries.setPreferenceStore(getPreferenceStore());
    }
    tab1.setControl(boundaries);

    Composite tab2contents = new Composite(tab, SWT.NONE);
    tab2.setControl(tab2contents);

    return tab;
  }

  public boolean performOk() {
    boolean boundariesOk = boundaries.performOk(getPreferenceStore());
    //TODO validate and store the values in the page's fields.
    System.out.println("Form ok? " + boundariesOk);
    return boundariesOk;
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
      IPreferenceStore store = new ScopedPreferenceStore(new ProjectScope(project), AutoGraderPlugin.PLUGIN_ID);
      initialiseDefaults(store);
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

  private static void initialiseDefaults(IPreferenceStore store) {
    float value = 95;
    for (Grade grade : Grade.values()) {
      store.setDefault("gradeboundaries."+grade.name()+".enabled", true);
      store.setDefault("gradeboundaries."+grade.name()+".value", value);
      value -= 3;
    }
  }

}
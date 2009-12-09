package ie.ucd.bon.plugin.config;

import ie.ucd.bon.plugin.BONPlugin;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.PropertyPage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class ProjectConfiguration extends PropertyPage implements IPropertyChangeListener {

  private static final int GRID_WIDTH = 3;
  
  private BONcBooleanFieldEditor buildHtml;
  private BONcFileFieldEditor htmlFile;
  private Composite composite;
  private IProject project;
  
	public ProjectConfiguration() {
		super();
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		composite = new Composite(parent, SWT.NONE);

		GridLayout layout = new GridLayout();
    layout.marginWidth = 3;
    layout.marginHeight = 3;
    layout.numColumns = GRID_WIDTH;
    composite.setLayout(layout);
		
		buildHtml = new BONcBooleanFieldEditor("buildHtml", "Generate html documentation?", composite);
		buildHtml.setPreferenceStore(getPreferenceStore());
		buildHtml.fillIntoGrid(composite, GRID_WIDTH);
		buildHtml.setPropertyChangeListener(this);
		htmlFile = new BONcFileFieldEditor("htmlFile", "File to generate", composite);
		htmlFile.setPreferenceStore(getPreferenceStore());
		htmlFile.fillIntoGrid(composite, GRID_WIDTH);
		htmlFile.setProject(project);
		
		return composite;
	}
	
	public boolean performOk() {
		boolean ok = true;
	  if (buildHtml.getBooleanValue()) {
	    File file = new File(htmlFile.getStringValue());
	    if (file.isDirectory()) {
	      ok = false;
	    } else {
	      file = file.getParentFile();
	      if (!file.exists()) {
	        ok = false;
	      }
	    }
	    
	    //TODO test we can write.
	  }
	  
		return ok;
	}
	
	@Override
  public void setElement(IAdaptable element) {
	  project = null;

    if (element instanceof IResource) {
      final IResource resource = (IResource)element;
      project = resource.getProject();
    } else if (element instanceof IJavaProject) {
      final IJavaProject jProject = (IJavaProject)element;
      project = jProject.getProject();
    }

    if (project != null) {
      IPreferenceStore store = new ScopedPreferenceStore(new ProjectScope(project), BONPlugin.PLUGIN_ID);
      //initialiseDefaults(store);
      setPreferenceStore(store);
      
      if (htmlFile != null) {
        htmlFile.setProject(project);
      }
    }
  }

	@Override
  public void setPreferenceStore(IPreferenceStore store) {
     super.setPreferenceStore(store);
     if (buildHtml != null) {
       buildHtml.setPreferenceStore(store);
     }
     if (htmlFile != null) {
       htmlFile.setPreferenceStore(store);
     }
  }

  public void propertyChange(PropertyChangeEvent event) {
    if (event.getSource() == buildHtml) {
      htmlFile.setEnabled(buildHtml.getBooleanValue(), composite);
    }
  }
	
	
	
}
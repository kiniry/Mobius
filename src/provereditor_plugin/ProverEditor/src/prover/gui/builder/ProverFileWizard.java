package prover.gui.builder;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

public class ProverFileWizard extends BasicNewResourceWizard{
	   private WizardNewFileCreationPage mainPage;
	   private String strTitle;
	   private String strDescription;
	   private String strExtension;
	   
	    /**
	     * Creates a wizard for creating a new file resource in the workspace.
	     */
	    public ProverFileWizard(String extension, String title, String description) {
	        super();
	        strExtension = extension;
	        strTitle = title;
	        strDescription = description;
	    }

	    /* (non-Javadoc)
	     * Method declared on IWizard.
	     */
	    public void addPages() {
	        super.addPages();
	        mainPage = new WizardNewFileCreationPage("newFilePage1", getSelection());//$NON-NLS-1$
	        mainPage.setTitle(strTitle);
	        mainPage.setDescription(strDescription); 
	        addPage(mainPage);
	    }

	    /* (non-Javadoc)
	     * Method declared on IWorkbenchWizard.
	     */
	    public void init(IWorkbench workbench, IStructuredSelection currentSelection) {
	        super.init(workbench, currentSelection);
	        setWindowTitle(strTitle);
	        setNeedsProgressMonitor(true);
	    }

	    /* (non-Javadoc)
	     * Method declared on BasicNewResourceWizard.
	     */
	    protected void initializeDefaultPageImageDescriptor() {
//	       ImageDescriptor desc = IDEWorkbenchPlugin.getIDEImageDescriptor("wizban/newfile_wiz.gif");//$NON-NLS-1$
//		   setDefaultPageImageDescriptor(desc);
	    }

	    /* (non-Javadoc)
	     * Method declared on IWizard.
	     */
	    public boolean performFinish() {
	    	String f = mainPage.getFileName();
	    	if(!f.endsWith(strExtension)) {
	    		mainPage.setFileName(f + strExtension);
	    	}
	        IFile file = mainPage.createNewFile();
	        if (file == null)
	            return false;

	        selectAndReveal(file);

	        // Open editor on new file.
	        IWorkbenchWindow dw = getWorkbench().getActiveWorkbenchWindow();
	        try {
	            if (dw != null) {
	                IWorkbenchPage page = dw.getActivePage();
	                if (page != null) {
	                    IDE.openEditor(page, file, true);
	                }
	            }
	        } catch (PartInitException e) {
//	            .openError(dw.getShell(), "Failed to open the file", 
//	                    e.getMessage(), e);
	        	e.printStackTrace();
	        }

	        return true;
	    }
}

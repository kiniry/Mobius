package fr.inria.everest.coq.sugar.builder;


import mobius.prover.gui.builder.ProjectNature;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;


public class CoqProjectWizard extends BasicNewProjectResourceWizard {

    public boolean performFinish() {
    	boolean res = super.performFinish();
    	if(!res) return false;
        IProject proj = getNewProject();
        try {
			IProjectDescription desc = proj.getDescription();
			String [] natures = desc.getNatureIds();
			String [] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = ProjectNature.NATURE_ID;
			desc.setNatureIds(newNatures);
			proj.setDescription(desc, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
        return true;
    }
}

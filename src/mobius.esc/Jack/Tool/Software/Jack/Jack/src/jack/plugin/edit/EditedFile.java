/*
 * Created on Jun 8, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jack.plugin.edit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;

/**
 *
 *  @author L. Burdy
 **/
public class EditedFile implements IEditedFile{
	
    String n;
    IProject p;
    
	/**
	 * @param file
	 */
	public EditedFile(String name, IProject project) {
		n = name;
		p = project;
	}
	
	/**
	 * @param jpo_file
	 */
	public EditedFile(IFile jpo_file) {
		n = jpo_file.getName();
		p = jpo_file.getProject();
	}

	public String getName() {
	return n;
	}
	
	public IProject getProject() {
	return p;
	}
}

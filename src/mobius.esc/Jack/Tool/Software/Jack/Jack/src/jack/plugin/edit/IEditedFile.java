/*
 * Created on Jun 8, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jack.plugin.edit;

import org.eclipse.core.resources.IProject;

/**
 *
 *  @author L. Burdy
 **/
public interface IEditedFile {

	/**
	 * @return
	 */
	String getName();

	/**
	 * @return
	 */
	IProject getProject();

}

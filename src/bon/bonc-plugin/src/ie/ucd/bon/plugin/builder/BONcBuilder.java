package ie.ucd.bon.plugin.builder;

import ie.ucd.bon.plugin.BONPlugin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class BONcBuilder extends IncrementalProjectBuilder {

  private static final String BUILDER_ID = BONPlugin.PLUGIN_ID + ".boncbuilder"; 
	
  protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
      throws CoreException {

    if (kind == IncrementalProjectBuilder.FULL_BUILD) {
      System.out.println("Full build");
    } else if (kind == IncrementalProjectBuilder.INCREMENTAL_BUILD) {
      System.out.println("Incremental Build");
    } else if (kind == IncrementalProjectBuilder.AUTO_BUILD) {
      System.out.println("Auto Build");
    }
    
    IResource[] resources = getProject().members();
    for (IResource resource : resources) {
      System.out.println("Resource: " + resource.getFullPath());
    }
    
    return null;
  }

  
  public static void addBuilderToProject(IProject project) {    // Cannot modify closed projects. 
	   if (!project.isOpen()) 
	      return; 
	   // Get the description. 
	   IProjectDescription description; 
	   try { 
	      description = project.getDescription(); 
	   } 
	   catch (CoreException e) { 
	      //FavoritesLog.logError(e); 
	      return; 
	   } 
	   // Look for builder already associated. 
	   ICommand[] cmds = description.getBuildSpec(); 
	   for (int j = 0; j < cmds.length; j++) 
	      if (cmds[j].getBuilderName().equals(BUILDER_ID)) 
	         return; 
	   // Associate builder with project. 
	   ICommand newCmd = description.newCommand(); 
	   newCmd.setBuilderName(BUILDER_ID); 
	   List<ICommand> newCmds = new ArrayList<ICommand>(); 
	   newCmds.addAll(Arrays.asList(cmds)); 
	   newCmds.add(newCmd); 
	   description.setBuildSpec( 
	      newCmds.toArray( 
	         new ICommand[newCmds.size()])); 
	   try { 
	      project.setDescription(description, null); 
	   } 
	   catch (CoreException e) { 
	      //FavoritesLog.logError(e); 
	   } 
	} 
  
}

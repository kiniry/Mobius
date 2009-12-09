package ie.ucd.bon.plugin.builder;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.plugin.BONPlugin;
import ie.ucd.bon.plugin.util.PluginUtil;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class BONcBuilder extends IncrementalProjectBuilder {

  private static final String BUILDER_ID = BONPlugin.PLUGIN_ID + ".boncbuilder";
  private static final String MARKER_ID = BONPlugin.PLUGIN_ID + ".bonclocproblemmarker";
  //private static final String NO_LOC_MARKER_ID = BONPlugin.PLUGIN_ID + ".boncproblemmarker";

  @SuppressWarnings("unchecked")
  protected IProject[] build(final int kind, final Map args, final IProgressMonitor monitor)
  throws CoreException {

    ResourcesPlugin.getWorkspace().run(
        new IWorkspaceRunnable() {
          public void run(IProgressMonitor monitor)
          throws CoreException
          {
            try {
              boncBuild(kind, monitor);
            } catch (CoreException e) {
              System.out.println("CoreException: " + e);
            }
          }
        },
        monitor
    );

    return null;
  }

  private void boncBuild(int kind, IProgressMonitor monitor) throws CoreException {
    if (kind == INCREMENTAL_BUILD || kind == AUTO_BUILD) {
      IResourceDelta delta = getDelta(getProject());
      if (delta != null) {
        BONResourceDeltaVisitor changeVisitor = new BONResourceDeltaVisitor();
        delta.accept(changeVisitor);

        if (changeVisitor.getChangedBonResources().size() == 0) {
          return;
        }
      }
    }

    List<IResource> bonResources = BONResourceVisitor.getBONResources(getProject());

    if (bonResources.size() == 0) {
      //No .bon files, don't run BONc
      return;
    }

    Map<File,IResource> pathResourceMap = PluginUtil.getResourceMap(bonResources);

    List<String> boncArgs = new ArrayList<String>();
    boncArgs.add("-i");
    boncArgs.add("-d");
    for (File file : pathResourceMap.keySet()) {
      boncArgs.add(file.getAbsolutePath());
    }

    getProject().deleteMarkers(MARKER_ID, false, IResource.DEPTH_INFINITE);

    Problems problems = Main.main2(boncArgs.toArray(new String[boncArgs.size()]), false);
    Collection<BONProblem> actualProblems = problems.getProblems();

    try {
      for (BONProblem bonProblem : actualProblems) {
        int severity;
        if (bonProblem.isError()) {
          severity = IMarker.SEVERITY_ERROR;
        } else if (bonProblem.isWarning()) {
          severity = IMarker.SEVERITY_WARNING;
        } else {
          severity = IMarker.SEVERITY_INFO;
        }
        SourceLocation location = bonProblem.getLocation();
        IMarker marker = PluginUtil.createMarker(getProject(), MARKER_ID, location, pathResourceMap, bonProblem.getMessage(), severity);
      }
    } catch (Exception e) {
      System.out.println("Exception: " + e);
      e.printStackTrace();
    }
  }

  public static void addBuilderToProject(IProject project) {    
    // Cannot modify closed projects. 
    if (!project.isOpen()) {
      return; 
    }

    // Get the description. 
    IProjectDescription description; 
    try { 
      description = project.getDescription(); 
    } 
    catch (CoreException e) {  
      return; 
    } 

    // Look for builder already associated. 
    ICommand[] cmds = description.getBuildSpec(); 
    for (int j = 0; j < cmds.length; j++) { 
      if (cmds[j].getBuilderName().equals(BUILDER_ID)) { 
        return; 
      }
    }

    // Associate builder with project. 
    ICommand newCmd = description.newCommand(); 
    newCmd.setBuilderName(BUILDER_ID);

    List<ICommand> newCmds = new ArrayList<ICommand>(); 
    newCmds.addAll(Arrays.asList(cmds)); 
    newCmds.add(newCmd); 
    description.setBuildSpec(newCmds.toArray(new ICommand[newCmds.size()])); 
    try { 
      project.setDescription(description, null); 
      project.build(FULL_BUILD, null);
    } catch (CoreException e) {
      return;
    } 
  } 

  public static void removeBuilderFromProject(IProject project) {
    // Cannot modify closed projects. 
    if (!project.isOpen()) {
      return; 
    }

    // Get the description. 
    IProjectDescription description; 
    try { 
      description = project.getDescription(); 
    } 
    catch (CoreException e) {  
      return; 
    } 

    // Disassociate builder with project. 
    ICommand[] cmds = description.getBuildSpec();
    List<ICommand> newCmds = new ArrayList<ICommand>(); 
    newCmds.addAll(Arrays.asList(cmds)); 

    boolean found = false;
    for (int i=0; i < cmds.length; i++) {
      if (newCmds.get(i).getBuilderName().equals(BUILDER_ID)) {
        newCmds.remove(i);
        found = true;
        break;  //Should never be associated twice
      }
    }

    if (found) {
      description.setBuildSpec(newCmds.toArray(new ICommand[newCmds.size()])); 
      try { 
        project.deleteMarkers(MARKER_ID, false, IResource.DEPTH_INFINITE);
        //project.deleteMarkers(NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);
        project.setDescription(description, null);
      } catch (CoreException e) {
        return;
      } 
    }
  }


}

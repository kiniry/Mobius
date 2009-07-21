package ie.ucd.bon.plugin.builder;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.BONWarning;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.plugin.BONPlugin;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;

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

  private static final boolean IS_WINDOWS = System.getProperty("os.name").toLowerCase().contains("win");
  
  private static final String BUILDER_ID = BONPlugin.PLUGIN_ID + ".boncbuilder";
  private static final String MARKER_ID = BONPlugin.PLUGIN_ID + ".bonclocproblemmarker";
  private static final String NO_LOC_MARKER_ID = BONPlugin.PLUGIN_ID + ".boncproblemmarker";

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

    if (kind == FULL_BUILD || kind == CLEAN_BUILD) {
      //System.out.println("Full build");
    } else if (kind == INCREMENTAL_BUILD || kind == AUTO_BUILD) {
      //System.out.println("Incremental Build");

      IResourceDelta delta = getDelta(getProject());
      if (delta != null) {
        BONResourceDeltaVisitor changeVisitor = new BONResourceDeltaVisitor();
        delta.accept(changeVisitor);

        if (changeVisitor.getChangedBonResources().size() == 0) {
          //System.out.println("No BON resources changed, not running BONc");
          return;
        }
      }

    }

    BONResourceVisitor visitor = new BONResourceVisitor();
    getProject().accept(visitor);

    List<IResource> bonResources = visitor.getBONResources();

    if (bonResources.size() == 0) {
      //No .bon files, don't run BONc
      return;
    }

    Map<String,IResource> pathResourceMap = new HashMap<String,IResource>();

    List<String> boncArgs = new ArrayList<String>();
    boncArgs.add("-i");
    boncArgs.add("-d");
    for (IResource bonResource : bonResources) {
      File file = bonResource.getLocation().toFile();
      String path = file.getAbsolutePath();
      boncArgs.add(path);

      pathResourceMap.put(path, bonResource);
    }

    //System.out.println("Deleting markers");
    getProject().deleteMarkers(MARKER_ID, false, IResource.DEPTH_INFINITE);
    getProject().deleteMarkers(NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);

    System.out.println("Bonc args: " + boncArgs.toString());
    try {
      Main.main2(boncArgs.toArray(new String[boncArgs.size()]), false);
    } catch (Exception e) {
      System.out.println("Exception whilst running BONc: " + e);
      e.printStackTrace();
    }
    Problems problems = Main.getProblems();
    SortedSet<BONProblem> actualProblems = problems.getProblems();


    try {
      for (BONProblem bonProblem : actualProblems) {

        SourceLocation location = bonProblem.getLocation();
        File file = location == null ? null : bonProblem.getLocation().getSourceFile();
        int lineNumber = location == null ? -1 : bonProblem.getLocation().getLineNumber();
        int charPositionStart = location == null ? -1 : bonProblem.getLocation().getAbsoluteCharPositionStart();
        int charPositionEnd = location == null ? -1 : bonProblem.getLocation().getAbsoluteCharPositionEnd();

        //Adjusting for different counting of line-ending characters between eclipse and antlr
        if (IS_WINDOWS && lineNumber != -1) {
          charPositionStart += (lineNumber -1);
          charPositionEnd += (lineNumber -1);
        }

        //System.out.println("File: " + file + ", line: " + lineNumber + ", char: (" + charPositionStart + ", " + charPositionEnd + ")");

        if (file != null && lineNumber > 0 && charPositionStart >= 0 && charPositionEnd >= 0) {

          IResource resource = pathResourceMap.get(file.getAbsolutePath());
          if (resource != null) {
            IMarker marker = resource.createMarker(MARKER_ID);
            marker.setAttribute(IMarker.MESSAGE, bonProblem.getMessage());
            marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
            marker.setAttribute(IMarker.CHAR_START, charPositionStart);
            marker.setAttribute(IMarker.CHAR_END, charPositionEnd + 1);

            if (bonProblem instanceof BONError) {
              marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
            } else if (bonProblem instanceof BONWarning) {
              marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
            }
          }                

        } else {
          //For the moment nothing.
          //TODO - how best to show an error without an associated location?
          IMarker marker = getProject().createMarker(NO_LOC_MARKER_ID);
          marker.setAttribute(IMarker.MESSAGE, bonProblem.getMessage());
          if (bonProblem instanceof BONError) {
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
          } else if (bonProblem instanceof BONWarning) {
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
          }
        }

      }
    } catch (Exception e) {
      System.out.println("Exception: " + e);
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
        project.deleteMarkers(NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);
        project.setDescription(description, null);
      } catch (CoreException e) {
        return;
      } 
    }
  }


}

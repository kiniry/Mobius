package mobius.prover.gui.builder.tagger;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import mobius.prover.Prover;
import mobius.prover.plugins.Logger;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;



public class Tagger {
  /** the current instance of the tagger. */
  public static final Tagger instance = new Tagger();  
  /** the file name of the file where the tags are stored. */
  public static final String fFilename = ".prover_editor_tags"; 
  
  /** the tags contained in the current selected project. */
  private TagTable fTags = new TagTable();
  /** the current selected project. */
  private IProject fProject;
  
  /**
   * @return the tags of the current project
   */
  public Iterator<TagStruct> getTags() {
    return fTags;
  }
  
  /**
   * Try to load tags from the project of a file.
   * @param f the file from which to start
   */
  public void run(final IFile f) {
    if (f == null) {
      return;
    }
    loadTags(f.getProject());
  }
  
  /**
   * Clean the build ie. remove the tag file from a given
   * project.
   * @param project the project from which the tag file will be removed
   */
  public static void performCleanBuild(final IProject project) {
    final IFile file = project.getFile(fFilename);
    final File tagfile = file.getRawLocation().toFile();
    tagfile.delete();
  }
  
  /**
   * Add the tag of the given file to the tag table.
   * @param f the file to find tags in
   */
  public void performAddChangedFile(final IFile f) {
    final IProject project = f.getProject();
    loadTags(project);
    try {
      tag(f.getRawLocation().toFile());
    } 
    catch (final IOException e) {
      Logger.err.println("Did not manage to read/write from the file " + f + " " + e);
    }
  }
  
  /**
   * If a file is removed from a project,
   * its tags too should be removed.
   * @param f the file to remove
   */
  public void performRemoveFile(final IFile f) {
    final IProject project = f.getProject();
    loadTags(project);
    fTags.remove(f.getRawLocation().toFile().toString());
  }
  
  /**
   * Build the tags for all the files in the whole project.
   * @param project the project to build the tags for
   */
  public void performFullBuild(final IProject project) {
    final File f = project.getLocation().toFile();
    tagDirectory(f);
    saveTags(project);  
  }
  
  /**
   * Load the tags from the given project.
   * @param project the project from which to load the tags
   */
  private void loadTags(final IProject project) {
    if (project == null || project.equals(fProject)) {
      return;
    }
    fProject = project;
    final IFile file = project.getFile(fFilename);
    final File tagfile = file.getRawLocation().toFile();
    if (file.exists()) {
      try {
        final ObjectInputStream ois = new ObjectInputStream(new FileInputStream(tagfile));
        fTags.load(ois);
        ois.close();
        
      } 
      catch (final IOException e) {
        Logger.err.println("There was a proble loading " + fFilename + ".");
      }
    }
    else {
      performFullBuild(project); 
    }    
  }

  /**
   * Save the tags for the given project.
   * @param project
   */
  private void saveTags(final IProject project) {
    final IFile file = project.getFile(fFilename);
    final File tagfile = file.getRawLocation().toFile();
    try {
      final ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(tagfile));
      fTags.save(oos);
      oos.close();
    } 
    catch (IOException e) {
      Logger.err.println("There was a problem saving " + fFilename + ".");
    }
    
    try {
      project.refreshLocal(IResource.DEPTH_ONE, null);
    } 
    catch (CoreException e) {
      Logger.warn.println("Could not refresh the view!");
    }
  }

  /**
   * Get tags from all the files of a directory.
   * It also goes recursively into the subdirectories.
   * @param f the directory to start from
   */
  private void tagDirectory(final File f) {
    final File [] dirs = f.listFiles(new FileFilter() {
      public boolean accept(final File pathname) {
        return pathname.isDirectory();
      }
    });
    final File [] files = f.listFiles(new FileFilter() {
      public boolean accept(final File pathname) {
        return pathname.getName().endsWith(".v");
      }
    });
    if (files != null) {
      for (int i = 0; i < files.length; i++) {
        try {
          tag(files[i]);
        } 
        catch (IOException e) {
          e.printStackTrace();
        }
      }
    }
    if (dirs != null) {
      for (int i = 0; i < dirs.length; i++) {
        tagDirectory(dirs[i]);
      }
    }
  }

  /**
   * Get the tag from a file, specific to a prover.
   * @param file the file to get the tag from
   * @throws IOException if there is a read error
   */
  private void tag(final File file) throws IOException {
    final Prover pr = Prover.findProverFromFile(file.toString());
    if (pr == null) {
      return;
    }
    final Pattern[][] pats = pr.getTranslator().getTagPatterns();
    final TagList l = new TagList();
    final ProverFileReader lnr = new ProverFileReader(new FileReader(file));
    String str;
    int offset = 0;
    final String filename = file.getAbsolutePath();
    while ((str = lnr.readLine()) != null) {
      
      final String old = str;
      for (int i = 0; i < pats.length; i++) {
        str = old;
        Matcher m = pats[i][0].matcher(str);
        if (m.find()) {
          final int wordbeg = m.end() + offset;
          str = str.substring(m.end());
          m = pats[i][1].matcher(str);
          m.find();
          str = str.substring(0, m.end());
//          int wordend = m.end() + wordbeg;
          l.add(new TagStruct(str, filename, wordbeg, str.length()));
          break;
        }
      }
      offset += lnr.getCount();
    }
    lnr.close();
    fTags.add(filename, l);
  }



  
}

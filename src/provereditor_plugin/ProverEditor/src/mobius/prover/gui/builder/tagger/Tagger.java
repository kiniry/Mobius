package mobius.prover.gui.builder.tagger;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import mobius.prover.Prover;
import mobius.prover.plugins.Logger;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;


/**
 * This class performs the handling of the tagging. 
 * It is used to load the tags, write the tags to disk.
 * @author J. Charles (julien.charles@inria.fr)
 */
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
      saveTags(project);
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
        final InputStream in = new FileInputStream(tagfile);
        fTags.load(in);
        in.close();
        
      } 
      catch (final IOException e) {
        Logger.err.println("There was a problem loading " + fFilename + ".");
      }
    }
    else {
      performFullBuild(project); 
    }    
  }

  /**
   * Save the tags for the given project.
   * @param project a valid project
   */
  private void saveTags(final IProject project) {
    final IFile file = project.getFile(fFilename);
    final File tagfile = file.getRawLocation().toFile();
    try {
      final OutputStream out = new FileOutputStream(tagfile);
      fTags.save(out);
      out.close();
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
   * Get all the tags from a file, specific to a prover, and put them
   * in the tags table.
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
    final ProverFileReader in = new ProverFileReader(new FileReader(file));
    final Path path = new Path(file.getAbsolutePath());
    String str;
    int offset = 0;
    int line = 0;
    while ((str = in.readLine()) != null) {
      line++;
      for (Pattern [] p: pats) {
        final TagStruct ts = match(str, p, path, line, offset);
        if (ts != null) {
          l.add(ts);
          break;
        }
        
      }
      offset += in.getCount();
    }
    in.close();
    fTags.add(file.getAbsolutePath(), l);
  }

  /**
   * Return the matching tag, if the given pattern matches.
   * @param str The String on which to match which is given from the
   * specified file
   * @param p the pattern to find
   * @param file the file on which the pattern matching is done
   * @param line the current line number in the file
   * @param offset the current offset at the beginning of the line
   * @return a valid tag, or null if the matching failed
   */
  private static TagStruct match(final String str, final Pattern [] p, 
                                 final Path file, 
                                 final int line, final int offset) {
    String text = str;
    final Matcher textMatch = p[0].matcher(text);
    if (textMatch.find()) {
      final int wordbeg = textMatch.start() + offset;
      String name = text.substring(textMatch.end());
      final Matcher nameMatch = p[1].matcher(name);
      if (nameMatch.find()) {
        name = name.substring(0, nameMatch.end());
        text = text.substring(textMatch.start(), 
                              textMatch.end() + nameMatch.end());
        return new TagStruct(name, file,
                             text, wordbeg, line);
      }
    }
    return null;
  }

}

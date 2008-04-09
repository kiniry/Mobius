
package mobius.prover.gui.builder.tagger;

import java.io.Serializable;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.plugins.Logger;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.ITextEditor;



/**
 * A data structure to store the tags. It contains the
 * file name, the beginning and the end of the word 
 * and the word to find back the word in a text...
 * Indeed it is a data structure to store some tags!
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class TagStruct implements Serializable {
  /** */
  private static final long serialVersionUID = 1L;
  /** the file name of the file where the tag can be found. */
  private final Path fFilename;  
  /** the length of the tag in the file. */
  private final int fLen;
  
  /** the text of the tag. */
  private final String fText;
  /** the word being tagged. */
  private final String fName;
  /** the beginning of the tag in the file. */
  private final int fBeg;
  /** the line number where to find the tag. */
  private final int fLine;
  
  /** the representation, it is static for convenience. */
  private final String fRepres;
  
  
  /**
   * Construct a tag. It has a name (the word of the tag)
   * the filename from where it come from, the beginning
   * of the tag in the file, the end of the tag in the
   * file
   * @param name the word being tagged
   * @param text the text of the tag
   * @param filename the name of the file where the tag has
   * been found
   * @param begin the beginning of the tag in the file
   * @param line the line numbre of the tag
   */
  public TagStruct (final String name, 
                    final Path filename,
                    final String text,
                    final int begin, 
                    final int line) {
    fText = text;
    fName = name;
    fBeg = begin;
    fLen = fText.length();
    fFilename = filename;
    fLine = line;
    fRepres = fText + "\u007f" + fName + "\u0001" + fLine + "," + fBeg  + "\n"; 
  }
  
  
  /**
   * Open an editor, and highlight the tag in the file.
   */
  public void show() {
    final IWorkbench bench = PlatformUI.getWorkbench();
    final IWorkbenchPage wp = bench.getActiveWorkbenchWindow().getActivePage();
    final IWorkspace ws = ResourcesPlugin.getWorkspace();
    final IFile f = ws.getRoot().getFileForLocation(fFilename);
    try {
      final IEditorPart ep = IDE.openEditor(wp, f, true);
      if (ep instanceof ProverEditor) {
        final ITextEditor te = (ITextEditor) ep;
        te.selectAndReveal(fBeg, fLen);
      }
    } 
    catch (PartInitException e) {
      Logger.err.println("Failed to initialize an editor for the file " + fFilename + ".");
      e.printStackTrace();
    }
    
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return fRepres;
  }

  /**
   * Returns the size of the representation.
   * @return A positive number
   */
  public int getSize() {
    return fRepres.getBytes().length; 
  }
  
  /**
   * Returns the word being tagged.
   * @return the content of the field {@link #fName}
   */
  public String getName() {
    return fName;
  }


  /**
   * Parse a tag structure from the given definition string.
   * @param fileName the current file name the tag belongs to
   * @param def the definition string from which to parse
   * @return a valid tag structure or null.
   */
  public static TagStruct parse(final String fileName, final String def) {
    if (def == null) {
      return null;
    }
    try {
      final String [] text = def.split("\u007f");
      final String [] name = text[1].split("\u0001");
      final String [] line = name[1].split(",");
      final int begin = Integer.parseInt(line[1]);    
      final TagStruct ts = new TagStruct(name[0], new Path(fileName),
                                         text[0], begin,
                                         Integer.parseInt(line[0]));
      return ts;
    }
    catch (ArrayIndexOutOfBoundsException e) {
      return null;
    }
  }
}

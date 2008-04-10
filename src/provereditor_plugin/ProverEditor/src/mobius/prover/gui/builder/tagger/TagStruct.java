
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
  /** the first delimiter for the definitions in the etags. */
  private static final byte FIRST_DELIMITER = 0x7f;
  /** the second delimiter for the definitions in the etags. */
  private static final byte SECOND_DELIMITER = 0x01;

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
  private final byte[] fRepres;
  
  
  
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
    fRepres = initRepres();
    
  }
  
  /**
   * Create the byte representation of the current tag structure.
   * It returns an etags compatible definition.
   * @return A ready to write etags definition
   */
  private byte[] initRepres() {
    final byte [] bText = fText.getBytes();
    final byte [] bName = fName.getBytes();
    final byte [] bLineOffs = (fLine + "," + fBeg).getBytes();
    final byte [] res = new byte [bText.length + 1 + bName.length + 1 + bLineOffs.length + 1];
    int offs = 0;
    System.arraycopy(bText, 0, res, 0, bText.length);
    offs += bText.length;
    res[offs] = FIRST_DELIMITER;
    offs++;
    System.arraycopy(bName, 0, res, offs, bName.length);
    offs += bName.length;
    res[offs] = SECOND_DELIMITER;
    offs++;
    System.arraycopy(bLineOffs, 0, res, offs, bLineOffs.length);
    offs += bLineOffs.length;
    res[offs] = '\n';
    return res;
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
    return new String(fRepres);
  }

  /**
   * Returns the size of the representation.
   * @return A positive number
   */
  public int getSize() {
    return fRepres.length; 
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
  public static TagStruct parse(final String fileName, final byte[] def) {
    if (def == null) {
      return null;
    }
    try {
      final int first = find(def, FIRST_DELIMITER);
      final int second = find(def, SECOND_DELIMITER);
      final byte[] text = new byte[first];
      final byte[] name = new byte[second - (first + 1)];
      final byte[] lineOffs = new byte[def.length - (second + 1)];
      
      System.arraycopy(def, 0, text, 0, text.length);
      System.arraycopy(def, first + 1, name, 0, name.length);
      System.arraycopy(def, second + 1, lineOffs, 0, lineOffs.length);
      
      final String [] tabLineOffs = new String(lineOffs).split(",");
      
      final TagStruct ts = new TagStruct(new String(name), 
                                         new Path(fileName),
                                         new String(text), 
                                         Integer.parseInt(tabLineOffs[1]),
                                         Integer.parseInt(tabLineOffs[0]));
      return ts;
    }
    catch (ArrayIndexOutOfBoundsException e) {
      return null;
    }
  }

  /**
   * Returns the index of the byte in the array or -1.
   * @param arr the array to look into
   * @param b the byte to search
   * @return a valid index or -1
   */
  private static int find(final byte[] arr, final byte b) {
    for (int i = 0; i < arr.length; i++) {
      if (arr[i] == b) {
        return i;
      }
    }
    return -1;
  }

  /**
   * Returns the definition of the current structure.
   * @return an array of bytes
   */
  public byte[] getBytes() {
    return fRepres;
  }
}

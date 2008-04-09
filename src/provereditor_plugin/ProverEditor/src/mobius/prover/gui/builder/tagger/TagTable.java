package mobius.prover.gui.builder.tagger;

import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;



/**
 * A tag table is the object that stores all the tags associated
 * with the file names. It enables to iterate of the tags
 * of all the files of the project, that's why it has iterator's
 * methods.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TagTable implements Iterator<TagStruct>, Serializable {
  /** */
  private static final long serialVersionUID = 1L;

  /** the list of tag files in the current project. */
  private List<TagFile> fListTagFiles = new ArrayList<TagFile>();
  /** the current file that is being checked for its tags. */
  private TagFile fCurrent;
  /** the iterator of the tag of the file that is currently selected. */
  private Iterator<TagStruct> fIter;
  /** the position of the currently selected file in the list of tag files. */
  private int fPos;
  

  /**
   * Adds or replace the file with the specified name
   * and associate it with its tags.
   * @param name the name of the file
   * @param tags the tags found in the file
   */
  public void add(final String name, final TagList tags) {
    final TagFile tf = new TagFile(name, tags);
    if ((fCurrent != null) && fCurrent.equals(tf)) {
      fListTagFiles.set(fPos, tf);
      fCurrent = tf;
      fIter = tf.iterator();
    }
    else {
      final int ind = fListTagFiles.indexOf(tf); 
      if (ind != -1) {
        fListTagFiles.set(ind, tf);
      }
      else {
        fListTagFiles.add(tf);
        if (fCurrent == null) {
          fIter = tf.iterator();
          fCurrent = tf;
        }
      }
    }
    
  }
  
  /**
   * Removes the tag file which has the specified name.
   * Or does nothing if the file cannot be found.
   * @param name the name of the tag file to remove
   */
  public void remove(final String name) {
    final int ind = fListTagFiles.indexOf(new TagFile(name)); 
    if (ind != -1) {
      fListTagFiles.remove(ind);
    }
  }
  

  /**
   * Unsupported operation.
   */
  @Override
  public void remove() {
    throw new UnsupportedOperationException();
  }

  
  /** {@inheritDoc} */
  @Override
  public boolean hasNext() {
    boolean res;
    if (fCurrent == null) {
      res = false;
    }
    else if (fIter.hasNext()) {
      res = true;
    }
    else {
      getNext();
      if (fPos == 0) {
        res = false;
      }
      else {
        res = fIter.hasNext();
      }
    }
    return res;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public TagStruct next() {
    return fIter.next();
  }
  
  
  /**
   * Move the current tag file to the next one,
   * change the current iterator, etc...
   */
  private void getNext() {
    if (fListTagFiles.size() > 0) {
      fPos++;
      fPos %= fListTagFiles.size();
      fCurrent = (TagFile)fListTagFiles.get(fPos);
      fIter = fCurrent.iterator();
    }
  }
  
  
  /**
   * Load a tag table from a file.
   * @param ois the stream from where to load the table
   * @throws IOException if there is a read error
   */
  public void load(final LineNumberReader ois) throws IOException {  
    fListTagFiles = new ArrayList<TagFile>();
    TagFile tf = null;
    while ((tf = TagFile.getTagFile(ois)) != null) {
      fListTagFiles.add(tf);      
    }
      
    if (fListTagFiles.size() > 0) {
      fCurrent = (TagFile)fListTagFiles.get(0);
      fIter = fCurrent.iterator();
    }
  }
    
    
  /**
   * Save the table of all the tags to a file 
   * on the disk, in the etags format.
   * @param out the print stream where to write the table
   */
  public void save(final PrintStream out) {
    for (TagFile t: fListTagFiles) {
      t.printHeader(out);
      t.printDefs(out);
    }
  }
  
  /**
   * All the tags for one specific file from the project.
   * @author J. Charles
   */
  private static final class TagFile implements Serializable {
    /** the magic number from the header. */
    private static final String HEADER_MAGIC_NUMBER = "\u000c";

    /** */
    private static final long serialVersionUID = 1L;
    
    /** the name of the file, used to differenciate 2 tag file. */
    private final String fName;
    /** the tags corresponding to the file. */
    private final TagStruct [] fTs;
    

    
    /**
     * Construct a new tag file from a file name and
     * a list of tags.
     * @param file the name of the file being treated
     * @param list the list of the tags of the file
     */
    public TagFile(final String file, final TagList list) {
      fName = file;
      final Iterator<TagStruct> iter = list.iterator();
      fTs = new TagStruct[list.size()];
      for (int i = 0; iter.hasNext(); i++) {
        fTs[i] = (TagStruct)iter.next();
      }
    }
    
    /**
     * Construct a new tag file with no tags 
     * associated with the file.
     * @param file the name of the file
     */
    public TagFile(final String file) {
      fName = file;
      fTs = new TagStruct[0];
    }
    
    /**
     * Return the tag file parsed from the given line number reader
     * or null.
     * @param ois The line number reader to read from
     * @return a valid tag file
     */
    public static TagFile getTagFile(final LineNumberReader ois) {
      final String [] strHeader = parseHeader(ois);
      if (strHeader == null) {
        return null;
      }
      final String fileName = strHeader[0];
      final int size  = Integer.parseInt(strHeader[1]);
      final TagList tl = parseDefinitions(ois, fileName, size);
      if (tl == null) {
        return null;
      }
      return new TagFile(fileName, tl);
    }

    /**
     * Parse the definition which is found in the given line number reader.
     * @param in the stream from which to read
     * @param file the file the series of tags belong to
     * @param size the max size to be read from the file
     * @return a valid tag list or null
     */
    private static TagList parseDefinitions(final LineNumberReader in, 
                                            final String file, final int size) {
      final TagList tl = new TagList();      
      int currentSize = 0;
      try {
        while (size > currentSize) {
          final String def = in.readLine();
          final TagStruct ts = TagStruct.parse(file, def);
          if (ts == null) {
            return null;
          }
          tl.add(ts);
          ts.getSize();
          currentSize += ts.getSize();
        }
      } 
      catch (IOException e) {
        return null;
      }
      return tl;
    }

    /**
     * Parse the header and returns an array of 2 elements, corresponding
     * to the header.
     * @param ois The stream from which to read the header
     * @return an array of 2 elements or null.
     * @throws IOException
     */
    private static String [] parseHeader(final LineNumberReader ois) {
      
      try {
        final String firstLine = ois.readLine();
        final String [] secondLine = ois.readLine().split(",");
        if ((HEADER_MAGIC_NUMBER.equals(firstLine)) &&
            (secondLine.length == 2)) {        
          return secondLine;
        }
      } 
      catch (IOException e) {
        return null;
      }  
      return null;
    }


    
    /**
     * Print the header of the tags to a file.
     * @param out the output stream where to print the header
     */
    public void printHeader(final PrintStream out) {
      final int size = getSizeDefs();
      out.println(HEADER_MAGIC_NUMBER);
      out.println(fName + "," + size);
    }

    /**
     * Get the size of the definitions. Used for the headers.
     * @return a positive number
     */
    private int getSizeDefs() {
      int res = 0;
      for (TagStruct ts: fTs) {
        res += ts.getSize();
      }
      return res;
    }

    /**
     * Prints the definitions to the given stream.
     * @param out the stream to print to
     */
    public void printDefs(final PrintStream out) {
      for (TagStruct ts: fTs) {
        out.print(ts.toString());
      }      
    }


    
    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object o) {
      return (o != null) && (o instanceof TagFile) && ((TagFile) o).fName.equals(fName);
    }
    
    /** {@inheritDoc} */
    @Override
    public int hashCode() {
      return fName.hashCode();
    }
    
    
    /**
     * Create an iterator over the array of tags of the
     * tag file.
     * @return an iterator of the field {@link #fTs}
     */
    public Iterator<TagStruct> iterator() {
      return new Iterator<TagStruct>() {
        /** the position in the table. */
        private int fPos;
        public void remove() { }
        
        public boolean hasNext() {
          return fPos < fTs.length;
        }

        public TagStruct next() {
          return fTs[fPos++];
        }
        
      };
      
    }
  }
}

package mobius.prover.gui.builder.tagger;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.prover.plugins.Logger;



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
  public void remove() {
    throw new UnsupportedOperationException();
  }

  
  /** {@inheritDoc} */
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
  public void load(final InputStream ois) throws IOException {  
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
  public void save(final OutputStream out) {
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
    private static final byte HEADER_MAGIC_NUMBER = 0x0c;

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
    public static TagFile getTagFile(final InputStream ois) {
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
    private static TagList parseDefinitions(final InputStream in, 
                                            final String file, final int size) {
      final TagList tl = new TagList();      
      int currentSize = 0;
      try {
        while (size > currentSize) {
          final byte[] def = readByteLine(in, size);
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
     * @param in The stream from which to read the header
     * @return an array of 2 elements or null.
     * @throws IOException
     */
    private static String [] parseHeader(final InputStream in) {
      
      try {
        final byte [] firstLine = new byte[2];
        final int res = in.read(firstLine);
        final String secondLine = readLine(in, 1024);
        if ((res == 2) && (firstLine[0] == HEADER_MAGIC_NUMBER) &&
              (firstLine[1] == '\n') &&
              secondLine != null) {
          return secondLine.split(",");
        }
      } 
      catch (IOException e) {
        return null;
      }  
      return null;
    }


    /**
     * Read a line from the stream. A line ends with the byte newline <code>'\n'</code>.
     * It uses a buffer of a specified size.
     * @param in the stream to read from
     * @param size the size of the intern buffer
     * @return an array of bytes trimmed to the correct length
     *  or <code>null</code> in case of errors.
     * @throws IOException if the reading fails
     */
    private static byte[] readByteLine(final InputStream in, 
                                       final int size) throws IOException {
      final byte[] buffer = new byte[size];
      for (int i = 0; i < buffer.length; i++) {
        final int b = in.read();
        if (b < 0) {
          return null;
        }
        buffer[i] = (byte) b;
        if (buffer[i] == '\n') {
          final byte[] strBuff = new byte[i];
          System.arraycopy(buffer, 0, strBuff, 0, i);
          return strBuff;
        }
      }
      return null;
    }
    
    /**
     * Read a line from the stream. A line ends with the byte newline <code>'\n'</code>.
     * It uses a buffer of a specified size.
     * @param in the stream to read from
     * @param size the size of the intern buffer
     * @return a valid String or <code>null</code> in case of errors.
     * @throws IOException if the reading fails
     */
    private static String readLine(final InputStream in, 
                                   final int size) throws IOException {
      final byte[] tab = readByteLine(in, size);
      if (tab != null) {
        return new String(tab);
      }
      return null;
    }
    

    /**
     * Print the header of the tags to a file.
     * @param out the output stream where to print the header
     */
    public void printHeader(final OutputStream out) {
      final int size = getSizeDefs();
      final byte [] firstLine = {HEADER_MAGIC_NUMBER, '\n'};
      final byte [] secondLine = (fName + "," + size).getBytes();
      
      try {
        out.write(firstLine);
        out.write(secondLine);
        out.write('\n');
      } 
      catch (IOException e) {
        Logger.err.println("Write errror!");
      }

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
     * @throws IOException 
     */
    public void printDefs(final OutputStream out) {
      for (TagStruct ts: fTs) {
        try {
          out.write(ts.getBytes());
        } 
        catch (IOException e) {
          Logger.err.println("Write Error!");
        }
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

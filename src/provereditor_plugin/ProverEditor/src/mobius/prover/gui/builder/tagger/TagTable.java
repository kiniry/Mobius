package mobius.prover.gui.builder.tagger;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
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
  public void load(final ObjectInputStream ois) throws IOException {
    try {
      
      final Object [] os = (Object []) ois.readObject();
      fListTagFiles = new ArrayList<TagFile>();
      for (int i = 0; i < os.length; i++) {
        fListTagFiles.add((TagFile)os[i]);
      }
    }  
    catch (ClassNotFoundException e) {
      Logger.err.println("I cannot find the an array class!");
    }
    if (fListTagFiles.size() > 0) {
      fCurrent = (TagFile)fListTagFiles.get(0);
      fIter = fCurrent.iterator();
    }
  }
  
  /**
   * Save the table of all the tags to a file 
   * on the disk.
   * @param oos the output stream where to write the tale
   * @throws IOException if there is a write error
   */
  public void save(final ObjectOutputStream oos) throws IOException {
    oos.writeObject(fListTagFiles.toArray());
  }  
  
  /**
   * All the tags for one specific file from the project.
   * @author J. Charles
   */
  private static final class TagFile implements Serializable {
    /** */
    private static final long serialVersionUID = 1L;
    
    /** the name of the file, used to differenciate 2 tag file. */
    public final String fName;
    /** the tags corresponding to the file. */
    public final TagStruct [] fTs;
    
    
    /**
     * Construct a new tag file from a file name and
     * a list of tags.
     * @param file the name of the file being treated
     * @param list the list of the tags of the file
     */
    public TagFile(final String file, final TagList list) {
      fName = file;
      final Iterator<TagStruct> iter = list.iterator();
      fTs = new TagStruct[list.list.size()];
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

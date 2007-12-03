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
 * @author J. Charles
 */
public class TagTable implements Iterator<TagStruct>, Serializable {
	/** */
	private static final long serialVersionUID = 1L;
	
	/** the list of tag files in the current project */
	private List<TagFile> listTagFiles = new ArrayList<TagFile>();
	/** the current file that is being checked for its tags */
	private TagFile current;
	/** the iterator of the tag of the file that is currently selected */
	private Iterator<TagStruct> iter;
	/** the position of the currently selected file in the list of tag files */
	private int pos = 0;
  

  /**
   * Adds or replace the file with the specified name
   * and associate it with its tags.
   * @param name the name of the file
   * @param tags the tags found in the file
   */
  public void add(String name, TagList tags) {
    TagFile  tf = new TagFile(name, tags);
    if((current != null) && current.equals(tf)) {
      listTagFiles.set(pos, tf);
      current = tf;
      iter = tf.iterator();
    }
    else {
      int ind; 
      if ((ind = listTagFiles.indexOf(tf)) != -1) {
        listTagFiles.set(ind, tf);
      }
      else {
        listTagFiles.add(tf);
        if(current == null) {
          iter = tf.iterator();
          current = tf;
        }
      }
    }
    
  }
  
  /**
   * Removes the tag file which has the specified name.
   * Or does nothing if the file cannot be found.
   * @param name the name of the tag file to remove
   */
  public void remove(String name) {
    int ind; 
    if ((ind = listTagFiles.indexOf(new TagFile(name))) != -1) {
      listTagFiles.remove(ind);
    }
  }
  

  /**
   * Unsupported operation.
   */
  /*
   * (non-Javadoc)
   * @see java.util.Iterator#remove()
   */
  public void remove() {
    throw new UnsupportedOperationException();
  }

  
  /*
   * (non-Javadoc)
   * @see java.util.Iterator#hasNext()
   */
  public boolean hasNext() {
    if(current == null)
      return false;
    if(iter.hasNext()) {
      return true;
    }
    else {
      getNext();
      if(pos == 0)
        return false;
      return iter.hasNext();
    }
  }
  
  
  /**
   * Iterate on the tags of the current selected file.
   */
  /*
   * (non-Javadoc)
   * @see java.util.Iterator#next()
   */
  public TagStruct next() {
    return iter.next();
  }
  
  
  /**
   * Move the current tag file to the next one,
   * change the current iterator, etc...
   */
  private void getNext() {
    if(listTagFiles.size() > 0) {
      pos ++;
      pos %= listTagFiles.size();
      current = (TagFile)listTagFiles.get(pos);
      iter = current.iterator();
    }
  }
  
  
  /**
   * Load a tag table from a file.
   * @param ois the stream from where to load the table
   * @throws IOException if there is a read error
   */
  public void load(ObjectInputStream ois) throws IOException {
    try {
      
      Object [] os = (Object []) ois.readObject();
      listTagFiles = new ArrayList<TagFile>();
      for(int i= 0; i < os.length; i++) {
        listTagFiles.add((TagFile)os[i]);
      }
    }  catch (ClassNotFoundException e) {
      Logger.err.println("I cannot find the an array class!");
    }
    if(listTagFiles.size() > 0) {
      current = (TagFile)listTagFiles.get(0);
      iter = current.iterator();
    }
  }
  
  /**
   * Save the table of all the tags to a file 
   * on the disk.
   * @param oos the output stream where to write the tale
   * @throws IOException if there is a write error
   */
  public void save(ObjectOutputStream oos) throws IOException {
    oos.writeObject(listTagFiles.toArray());
  }  
  
  /**
   * All the tags for one specific file from the project.
   * @author J. Charles
   */
  private static final class TagFile implements Serializable {
    /** */
    private static final long serialVersionUID = 1L;
    
    /** the name of the file, used to differenciate 2 tag file */
    public final String name;
    /** the tags corresponding to the file */
    public final TagStruct [] ts;
    
    
    /**
     * Construct a new tag file from a file name and
     * a list of tags.
     * @param file the name of the file being treated
     * @param list the list of the tags of the file
     */
    public TagFile(String file, TagList list) {
      name = file;
      Iterator<TagStruct> iter = list.iterator();
      ts = new TagStruct[list.list.size()];
      for(int i = 0; iter.hasNext(); i++) {
        ts[i] = (TagStruct)iter.next();
      }
    }
    
    
    /**
     * Construct a new tag file with no tags 
     * associated with the file
     * @param file the name of the file
     */
    public TagFile(String file) {
      name = file;
      ts = new TagStruct[0];
    }
    
    
    /**
     * Check if the name of 2 tag file is the same.
     */
    /*
     * (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    public boolean equals(Object o) {
      return (o != null) && (o instanceof TagFile) && ((TagFile) o).name.equals(name);
    }
    
    /**
     * Returns the hash code of {@link #name}
     */
    /*
     * (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    public int hashCode() {
      return name.hashCode();
    }
    
    
    /**
     * Create an iterator over the array of tags of the
     * tag file.
     * @return an iterator of the field {@link #ts}
     */
    public Iterator<TagStruct> iterator() {
      return new Iterator<TagStruct>() {
        int pos;
        public void remove() {
          
        }

        public boolean hasNext() {
          return pos < ts.length;
        }

        public TagStruct next() {
          return ts[pos++];
        }
        
      };
      
    }
  }
}

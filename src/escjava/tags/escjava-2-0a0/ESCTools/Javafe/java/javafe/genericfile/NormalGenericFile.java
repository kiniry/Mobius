/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.genericfile;


import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;


/**
 * A NormalGenericFile represents a normal file (java.io.File) as a
 * GenericFile.
 */

public class NormalGenericFile extends File implements GenericFile {

    /***************************************************
     *                                                 *
     * Creation:				       *
     *                                                 *
     **************************************************/

    /**
     * Create a NormalGenericFile to represent an existing File. <p>
     *
     * <esc> requires underlyingFile!=null </esc>
     */
    public NormalGenericFile(File underlyingFile) {
	super(underlyingFile.getPath());
    }


    /** Create a NormalGenericFile from a filename */
    //@ requires name!=null    
    public NormalGenericFile(String name) {
	super(name);
    }


    /***************************************************
     *                                                 *
     * New Operations:				       *
     *                                                 *
     **************************************************/

    /**
     * Return a name that uniquely identifies us to the user.
     *
     * Warning: the result may not be a conventional filename or use
     * the system separators.
     */
    public String getHumanName() {
	return this.toString();
    }


    /**
     * Return a String that canonically represents the identity of our
     * underlying file.
     *
     * This function must be defined such that if two GenericFiles
     * return non-null canonical ID's then the IDs are the same
     * (modulo .equals) => the GenericFiles represent the same
     * underlying file.  Ideally, under normal circumstances, the =>
     * is actually a <=>.
     *
     * This function should only return null in exceptional
     * cases, such as when an I/O error in the underlying storage media
     * prevents construction of a canonical ID.
     *
     * Convention: Canonical IDs start with <X> where X is the
     * fully-qualified name of the class that mediates I/O to the
     * underlying file.  E.g., java.io.File for a normal disk file.
     */
    public String getCanonicalID() {
	try {
	    return "<java.io.File>" + this.getCanonicalPath();
	} catch (IOException e) {
	    return null;
	}
    }


    /**
     * Return our local name, the name that distinguishes us
     * within the directory that contains us.
     *
     * E.g., "/a/b/c" has local name "c", "/e/r/" has local name "r", and
     * "/" has local name "".  (assuming "/" is the separator char)
     */
    public String getLocalName() { return getName(); }


    /**
     * Open the file we represent as an InputStream.<p>
     *
     * java.io.IOEXception may be thrown for many reasons, including no
     * such file and read permission denied.<p>
     */
    public InputStream getInputStream() throws IOException {
	return new FileInputStream(this);
    }


    /**
     * Attempt to return a GenericFile that describes the file in the
     * same "directory" as us that has the local name <code>n</code>. <p>
     *
     * No attempt is made to verify whether or not that file exists.<p>
     *
     * In cases where the notion of "containing directory" makes no
     * sense (e.g., streams or root directories), null is returned.
     */
    public GenericFile getSibling(String n) { 
	String dir = super.getParent();
	if (dir==null)
	    return null;

	return new NormalGenericFile(dir + separator + n);
    }
}

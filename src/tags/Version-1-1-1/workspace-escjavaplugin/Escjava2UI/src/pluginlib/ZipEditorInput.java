/*
 * This file is part of the Esc/Java2 plugin project. Copyright 2004 David R.
 * Cok
 * 
 * Created on Feb 5, 2005
 */
package pluginlib;

import java.io.IOException;
import java.util.zip.ZipFile;

import org.eclipse.core.resources.IStorage;
import org.eclipse.debug.core.sourcelookup.containers.ZipEntryStorage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;

/**
 * This class is used to provide an IEditorInput from
 * files that are in a jar file, so that entries in
 * a jar file can be displayed (readonly) in an editor
 * within Eclipse.
 * 
 * @author David R. Cok
 */
public class ZipEditorInput implements IStorageEditorInput {

  /**
   * Cached value corresponding to the entry in the Zip file
   */
  //@ non_null
  final private ZipEntryStorage s;

  /** Constructor to wrap the zip file entry for the editor
   * @param zes The zip file entry destined for the editor
   */
  public ZipEditorInput(/*@ non_null */ ZipEntryStorage zes) {
    s = zes;
  }
  
  /** Constructor to wrap an element of the zip file for the editor
   * @param jarFileName   The name of the zip or jar file in which the element resides
   * @param jarEntryName  The file name of the entry within the zip /jar file
   * @throws IOException
   */
  public ZipEditorInput(String jarFileName, String jarEntryName) 
  		throws IOException {
    ZipFile z = new ZipFile(jarFileName);
    s = new ZipEntryStorage(z,z.getEntry(jarEntryName));
  }

  public Object getAdapter(Class c) {
    // There are requests to adpat this object to IFile,
    // IResource, ILocationProvider.  Since there is not
    // a file system entity to point to and since we do not
    // want to add the zip entry to the project, we decline
    // all requests.  No harm seems to happen.
    return null;
  }

  /** 
   * @see java.lang.Object#equals(java.lang.Object)
   * 
   * @return true if the objects refer to the same entry of the same zip file
   */
  public boolean equals(Object o) {
    if (!(o instanceof ZipEditorInput)) return false;
    ZipEditorInput z = (ZipEditorInput)o;
    return s.getFullPath().equals(z.s.getFullPath());
  }

  
  /** Returns the IStorage object represented by this.
   * @return The underlying IZipEntryStorage object
   */
  public IStorage getStorage() {
    return s;
  }

  /** @see org.eclipse.ui.IEditorInput#getName()
   * 
   * @return a display name for the object
   */
  public String getName() {
    return s.getName();
  }

  /** @see org.eclipse.ui.IEditorInput#exists()
   * @return false since the object does not exist in the project
   */
  public boolean exists() {
    return false;
  }

  /** @see org.eclipse.ui.IEditorInput#getImageDescriptor()
   * @return null since this method is sort of inapplicable
   */
  public ImageDescriptor getImageDescriptor() {
    return null;
  }

  /** @see org.eclipse.ui.IEditorInput#getPersistable()
   * @return null since the object is readonly
   */
  public IPersistableElement getPersistable() {
    return null;
  }

  /** @see org.eclipse.ui.IEditorInput#getToolTipText()
   * @return some help type text consisting of the file and entry names
   */
  public String getToolTipText() {
    return s.getName();
  }

}
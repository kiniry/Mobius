package mobius.bico.bicolano.coq;

import java.io.File;

/**
 * A small structure to represent a load path.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class LoadPath {
  /** the path the load path represents. */
  private String fPath;
  
  /**
   * Constructs a loadpath out of a path.
   * @param path the path which is the load path
   */
  public LoadPath(final String path) {
    fPath = path;
  }

  /** {@inheritDoc} */
  @Override
  public boolean equals (final Object o) {
    return (o instanceof LoadPath) &&
            fPath.equals(((LoadPath) o).fPath);
  }
  
  /** {@inheritDoc} */
  @Override
  public int hashCode() {
    return fPath.hashCode();
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return fPath;
  }

  /**
   * Returns the path relative to the given working dir.
   * @param workingDir a working dir the relative path has to
   * be calculated from.
   * @return a relative path
   */
  public String getRelative(final File workingDir) {
    final String [] tabPath = fPath.split(File.separator);
    final String [] tabWrk = workingDir.toString().split(File.separator);
    
    String res = "";
    int i;
    for (i = 0; i < tabPath.length && i < tabWrk.length; i++) {
      if (!tabPath[i].equals(tabWrk[i])) {
        break;
      }
    }
    
    if (i < tabWrk.length) {
      for (int j = i; j < tabWrk.length; j++) {
        res += ".." + File.separator;
      }
    }
    
    for (int j = i; j < tabPath.length; j++) {
      res += tabPath[j] + File.separator;
    }
    return res;
  }
  
  /**
   * For testing purpose only.
   * @param args ignored
   */
  public static void main (final String[] args) {
    final LoadPath lp = new LoadPath("/home/julien/jesaispas");
    System.out.println(lp.getRelative(new File("/home/")));

    System.out.println(lp.getRelative(new File("/home/julien/franchement/")));
  }
  

}

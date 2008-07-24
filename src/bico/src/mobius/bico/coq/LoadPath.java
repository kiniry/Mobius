package mobius.bico.coq;

import java.io.File;

import mobius.bico.executors.Constants.Syntax;

public class LoadPath {
  /** the path the load path represents. */
  private String fPath;
  
  public LoadPath(final String path) {
    fPath = path;
  }

  public String print() {
    return print(fPath.toString());
  }
  
  public String print(String path) {
    return Syntax.ADD_LOAD_PATH + " \"" + path +  "\".\n"; 
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
    return fPath.toString();
  }

  
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

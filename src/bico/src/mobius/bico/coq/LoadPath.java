package mobius.bico.coq;

import java.io.File;

import mobius.bico.executors.Constants;

public class LoadPath {
  private String fPath;
  
  public LoadPath(final String path) {
    fPath = path;
  }

  public String print() {
    return print(fPath.toString());
  }
  
  public String print(String path) {
    return Constants.ADD_LOAD_PATH + " \"" + path +  "\".\n"; 
  }

  
  public String toString() {
    return fPath.toString();
  }

  public String printRelative(File workingDir) {
    final String [] tabPath = fPath.split(File.separator);
    final String [] tabWrk = workingDir.toString().split(File.separator);
    
    String res = "";
    for (String part: tabWrk) {
      
    }
    return null;
  }
}

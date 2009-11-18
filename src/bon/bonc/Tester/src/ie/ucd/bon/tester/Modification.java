package ie.ucd.bon.tester;

import java.io.File;
import java.util.List;

public interface Modification {

  void modify(StringBuilder string, List<Pair<File,String>> otherInputs);
  
}

package ie.ucd.autograder.builder.markercollectors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class CheckstyleMarkerCollector extends MarkerCollector {

  //Taken from the eclipse-cs plugin.xml file
  //http://eclipse-cs.cvs.sourceforge.net/viewvc/eclipse-cs/CheckstylePlugin/plugin.xml
  public static final String CHECKSTYLE_MARKER = "com.atlassw.tools.eclipse.checkstyle.CheckstyleMarker";
    
  private static final List<String> types = new ArrayList<String>(1);
  static {
    types.add(CHECKSTYLE_MARKER);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

}

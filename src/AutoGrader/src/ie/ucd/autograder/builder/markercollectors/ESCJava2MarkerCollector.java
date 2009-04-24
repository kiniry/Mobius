package ie.ucd.autograder.builder.markercollectors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class ESCJava2MarkerCollector extends MarkerCollector {

  //Taken from the ESC/Java2 plugin.xml file
  //https://mobius.ucd.ie/trac/browser/src/escjava_plugin/Escjava2UI/plugin.xml
  public static final String ESC_MARKER = "mobius.escjava2.plugin.escjavaWarningMarker";
  
  private static final List<String> types = new ArrayList<String>(1);
  static {
    types.add(ESC_MARKER);
  }
  
  @Override
  public Collection<String> getTypes() {
    return types;
  }

}

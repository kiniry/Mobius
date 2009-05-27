package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;

import java.util.HashMap;
import java.util.Map;

public class BONST {

  public final Map<String,Cluster> clusters = new HashMap<String,Cluster>();
  public final Map<String,Clazz> classes = new HashMap<String,Clazz>();
  
  
}

package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;

import java.util.Stack;

public class VisitorContext {

  public Clazz clazz = null;
  
  public final Stack<Cluster> clusterStack = new Stack<Cluster>();
  
}

package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.graph.Graph;

import java.util.HashMap;
import java.util.Map;

public class BONST {

  public final Map<String,Cluster> clusters = new HashMap<String,Cluster>();
  public final Map<String,Clazz> classes = new HashMap<String,Clazz>();
  
  public final Graph<String,BONType> classInheritanceGraph = new Graph<String,BONType>();
  public final Graph<String,String> simpleClassInheritanceGraph = new Graph<String,String>();
  
  public final Map<AstNode,Indexing> indexing = new HashMap<AstNode,Indexing>();
  
}

package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.graph.Graph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class BONST {

  public final Map<String,Cluster> clusters = new HashMap<String,Cluster>();
  public final Map<String,Clazz> classes = new HashMap<String,Clazz>();
  
  public final Graph<String,BONType> classInheritanceGraph = new Graph<String,BONType>();
  public final Graph<String,String> simpleClassInheritanceGraph = new Graph<String,String>();
  
  public final Graph<String,Cluster> classClusterGraph = new Graph<String,Cluster>();
  public final Graph<String,Cluster> clusterClusterGraph = new Graph<String,Cluster>();
  
  public final Map<AstNode,Indexing> indexing = new HashMap<AstNode,Indexing>();
  
  public final Collection<ClientRelation> clientRelations = new ArrayList<ClientRelation>();
  
  public final BONSTInformal informal = new BONSTInformal();
  
  public class BONSTInformal {
    
    public final Map<String,ClusterChart> clusters = new HashMap<String,ClusterChart>();
    public final Map<String,ClassChart> classes = new HashMap<String,ClassChart>();  
   
    public final Graph<String,ClusterChart> classClusterGraph = new Graph<String,ClusterChart>();
    public final Graph<String,ClusterChart> clusterClusterGraph = new Graph<String,ClusterChart>();
    
    public final Graph<ClassChart,String> classInheritanceGraph = new Graph<ClassChart,String>();
    
    public final Graph<String,String> descriptionGraph = new Graph<String,String>();
    
    public ClusterChart systemChart;
    
  }
  
}

package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.graph.Graph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class BONST {

  public final Map<String,Cluster> clusters = new HashMap<String,Cluster>();
  public final Map<String,Clazz> classes = new HashMap<String,Clazz>();
  
  public final Graph<String,Type> classInheritanceGraph = new Graph<String,Type>();
  public final Graph<String,String> simpleClassInheritanceGraph = new Graph<String,String>();
  public final Graph<String,Cluster> classClusterGraph = new Graph<String,Cluster>();
  public final Graph<String,Cluster> clusterClusterGraph = new Graph<String,Cluster>();
  
  public final TwoDimensionalMap<Clazz, String, FeatureSpecification> featuresMap = new TwoDimensionalMap<Clazz,String,FeatureSpecification>();
  public final Map<FeatureSpecification,List<ClassName>> selectiveExportMap = new HashMap<FeatureSpecification,List<ClassName>>();
  
  public final Map<AstNode,Indexing> indexing = new HashMap<AstNode,Indexing>();
  public final Collection<ClientRelation> clientRelations = new ArrayList<ClientRelation>();  
  
  public final Map<AstNode,Type> typeMap = new HashMap<AstNode,Type>();
  
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
  
  
  public boolean isSubtypeOrEqual(Type type1, Type type2) {
    //If one type is null
    if ((type1 == null && type2 != null) || (type2 == null && type1 != null)) {
      return false;
    }
    //TODO using .equals here, which will do exact instance comparison.
    //This is fine so long as type instances are unique for a given type
    if (type1.equals(type2)) {
      return true;
    } else {
      //If all generics are equal
      if (type1.getActualGenerics().equals(type2.getActualGenerics())) {
        //If one of the parents are a subtype or equal...
        Collection<Type> parents = classInheritanceGraph.get(type1.getIdentifier());
        for (Type parent : parents) {
          if (isSubtypeOrEqual(parent, type2)) {
            return true;
          }
        }
        //No parents are a subtype or equal
        return false;
      } else {
        return false;
      }
    }
  }
}

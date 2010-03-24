/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.util.TwoDimensionalMap;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class BONST {

  /** A map from cluster name (String) to the corresponding Cluster AST Node. */
  public final Map<String,Cluster> clusters = new HashMap<String,Cluster>();

  /** A map from class name (String) to the corresponding Clazz AST Node. */
  public final Map<String,Clazz> classes = new HashMap<String,Clazz>();

  public final Graph<String,Type> classInheritanceGraph = new Graph<String,Type>();
  /** Inheritance graph with generics elided. Nodes are class names, edges go from a subclass to the parent class. */
  public final Graph<String,String> simpleClassInheritanceGraph = new Graph<String,String>();
  
  /** A map from class name (String) to the Cluster AST node that contains the class */
  public final Graph<String,Cluster> classClusterMap = new Graph<String,Cluster>();
  /** A map from cluster name (String) to the Cluster AST node that contains the cluster. */
  public final Graph<String,Cluster> clusterClusterGraph = new Graph<String,Cluster>();

  public final Map<String,Type> classNameToTypeMap = new HashMap<String,Type>();
  public final TwoDimensionalMap<Clazz, String, FeatureSpecification> featuresMap = new TwoDimensionalMap<Clazz,String,FeatureSpecification>();
  public final Map<FeatureSpecification,Clazz> featureDeclaringClassMap = new HashMap<FeatureSpecification,Clazz>();
  public final Map<FeatureSpecification,List<ClassName>> selectiveExportMap = new HashMap<FeatureSpecification,List<ClassName>>();
  public final Map<FeatureSpecification,List<String>> selectiveExportStringsMap = new HashMap<FeatureSpecification,List<String>>();
  public final Map<FeatureSpecification,Boolean> selectiveExportPrivateMap = new HashMap<FeatureSpecification,Boolean>();

  public final Map<Clazz,List<FormalGeneric>> genericsMap = new HashMap<Clazz,List<FormalGeneric>>();
  public final TwoDimensionalMap<Clazz, String, FormalGeneric> genericNamesMap = new TwoDimensionalMap<Clazz, String, FormalGeneric>();
  public final Map<Clazz,List<Type>> filledInGenericsMap = new HashMap<Clazz,List<Type>>();
  public final TwoDimensionalMap<Clazz, String, Type> filledInGenericNamesMap = new TwoDimensionalMap<Clazz, String, Type>();

  /** Maps individual AST nodes to their corresponding indexing clause. */
  public final Map<AstNode,Indexing> indexing = new HashMap<AstNode,Indexing>();
  /** All the client relations defined in the input. */
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
}

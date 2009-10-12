package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.Type;

import java.util.List;
import java.util.Stack;

public class VisitorContext {

  public Clazz clazz = null;
  public ClusterChart clusterChart = null;
  public final Stack<Cluster> clusterStack = new Stack<Cluster>();

  public List<ClassName> selectiveExport = null;
  public List<String> selectiveExportStrings = null;
  public boolean selectiveExportPrivate = false;

  public Type callQualifier = null;
}

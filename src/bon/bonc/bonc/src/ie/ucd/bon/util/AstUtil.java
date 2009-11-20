package ie.ucd.bon.util;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.source.SourceLocation;

public class AstUtil {

  public static SourceLocation getReportingSourceLocation(AstNode node) {
    SourceLocation loc = node.getLocation();
    if (node instanceof Clazz) {
      return ((Clazz)node).name.getLocation();
    } else if (node instanceof Cluster) {
      return loc.mutableClone().setAbsoluteCharPositionEnd(loc.getAbsoluteCharPositionStart() + 7 + ((Cluster)node).name.length())
                               .setAbsoluteCharPositionStart(loc.getAbsoluteCharPositionStart() + 8);
    } else if (node instanceof StaticDiagram) {
      StaticDiagram sd = (StaticDiagram)node;
      return loc.mutableClone().setAbsoluteCharPositionEnd(loc.getAbsoluteCharPositionStart() + 15 + (sd.extendedId==null?0:sd.extendedId.length()));
    } else if (node instanceof FeatureSpecification) {
      FeatureSpecification fSpec = (FeatureSpecification)node;
      return new SourceLocation(fSpec.featureNames.get(0).getLocation(),fSpec.featureNames.get(fSpec.featureNames.size()-1).getLocation());
    } else if (node instanceof ClassChart) {
      return ((ClassChart)node).name.getLocation();
    } else if (node instanceof ClusterChart) {
      //TODO clustername should be an AST node with a location associated
      ClusterChart cluster = (ClusterChart)node;
      return loc.mutableClone().setAbsoluteCharPositionStart(loc.getAbsoluteCharPositionStart()+8).setAbsoluteCharPositionEnd(loc.getAbsoluteCharPositionStart()+8+cluster.name.length());
    } else {
      return loc;
    }
    //TODO complete this and use for BONProblem instantiations
  }
  
  public static Converter<AstNode,String> nodeToStringConverter = new Converter<AstNode,String>() {
    public String convert(AstNode toConvert) {
      return StringUtil.prettyPrint(toConvert);
    }
  };
  
}

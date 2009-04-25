package ie.ucd.autograder.metrics;

public class MetricsConstants {

  public static class IdName {
    public final String id;
    public final String name;
    public IdName(String id, String name) {
      this.id = id;
      this.name = name;
    }    
  }
  
  //Constants taken from the metrics plugin.xml (extract in metricsids.xml)
  //Does not appear to be complete. In particular TLOC was added from the source
  
  //From printing the metrics used (displayed) by default by the plugin:
  // Ids: NORM, NOF, NSC, NOC, MLOC, NOM, NBD, DIT, NOP, CA, NOI, VG, TLOC, RMI, PAR, LCOM, CE, NSM, RMD, RMA, SIX, WMC, NSF
  // Descriptions: Number of Overridden Methods, Number of Attributes, Number of Children, Number of Classes, Method Lines of Code, Number of Methods, Nested Block Depth, Depth of Inheritance Tree, Number of Packages, Afferent Coupling, Number of Interfaces, McCabe Cyclomatic Complexity, Total Lines of Code, Instability, Number of Parameters, Lack of Cohesion of Methods, Efferent Coupling, Number of Static Methods, Normalized Distance, Abstractness, Specialization Index, Weighted methods per Class, Number of Static Attributes
  
  //Also from net.sourceforge.metrics.core.Constants 
  
  public static final IdName NumberOfOverriddenMethods = new IdName("NORM", "Number of Overridden Methods");
  public static final IdName NumberOfAttributes = new IdName("NOF", "Number of Attributes");
  public static final IdName NumberOfChildren = new IdName("NSC", "Number of Children");
  public static final IdName NumberOfClasses = new IdName("NOC", "Number of Classes");
  public static final IdName MethodLinesOfCode = new IdName("MLOC", "Method Lines of Code");
  public static final IdName NumberOfMethods = new IdName("NOM", "Number of Methods");
  public static final IdName NestedBlockDepth = new IdName("NBD", "Nested Block Depth");
  public static final IdName DepthOfInheritanceTree = new IdName("DIT", "Depth of Inheritance Tree"); 
  public static final IdName NumberOfPackages = new IdName("NOP", "Number of Packages");
  public static final IdName AfferentCoupling = new IdName("CA", "Afferent Coupling");
  public static final IdName NumberOfInterfaces = new IdName("NOI", "Number of Interfaces");
  public static final IdName McCabeCyclomaticComplexity = new IdName("VG", "McCabe Cyclomatic Complexity");
  public static final IdName TotalLinesOfCode = new IdName("TLOC", "Total Lines of Code");
  public static final IdName Instability = new IdName("RMI", "Instability");
  public static final IdName LackOfCohesionOfMethods = new IdName("LCOM", "Lack of Cohesion of Methods");
  public static final IdName EfferentCoupling = new IdName("CE", "Efferent Coupling");
  public static final IdName NumberOfStaticMethods = new IdName("NSM", "Number of Static Methods");
  public static final IdName NormalizedDistance = new IdName("RMD", "Normalized Distance");
  public static final IdName Abstractness = new IdName("RMA", "Abstractness");
  public static final IdName SpecializationIndex = new IdName("SIX", "Specialization Index");
  public static final IdName WeightedMethodsPerClass = new IdName("WMC", "Weighted methods per Class");
  public static final IdName NumberOfStaticAttributes = new IdName("NSF", "Number of Static Attributes");
  
  public static IdName[] METRICS = { TotalLinesOfCode, McCabeCyclomaticComplexity, MethodLinesOfCode };
}

package ie.ucd.autograder.grading;

import ie.ucd.autograder.util.Pair.MarkGradePair;

import java.util.Arrays;
import java.util.List;

public class GradeLookupTable {

  private final List<MarkGradePair> gradeBoundaries;

  public GradeLookupTable(MarkGradePair[] gradeBoundaries) {
    this(Arrays.asList(gradeBoundaries));
  }

  public GradeLookupTable(List<MarkGradePair> gradeBoundaries) {
    //TODO sort, to ensure we get the right grade
    this.gradeBoundaries = gradeBoundaries;
  }

  public Grade toGrade(double mark) {

    for (MarkGradePair boundary : gradeBoundaries) {
      if (mark >= boundary.getFirst()) {
        return boundary.getSecond();
      }
    }
    System.out.println("No grade found for mark " + mark + "!");
    System.out.println("Boundaries: " + gradeBoundaries);
    assert false; //Final boundary should always have a mark of zero!
    return null;
  }

  //FindBugs per 1000 NCSS: 0-10 (very good), 10-50 (good), 50-100 (ok), 100-250 (poor), 250- (very poor)
  public static final GradeLookupTable FINDBUGS_WARNING_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(250.0,Grade.F),
       new MarkGradePair(100.0,Grade.D),
       new MarkGradePair(50.0,Grade.C),
       new MarkGradePair(10.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );

  //FindBugs per 1000 NCSS: 0-10 (very good), 10-50 (good), 50-100 (ok), 100-250 (poor), 250- (very poor)
  public static final GradeLookupTable FINDBUGS_ERROR_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(250.0,Grade.F),
       new MarkGradePair(100.0,Grade.D),
       new MarkGradePair(50.0,Grade.C),
       new MarkGradePair(10.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );
  
  //PMD warnings per 1000 NCSS: 0-10 (very good), 10-50 (good), 50-100 (ok), 100-250 (poor), 250-500 (very poor), 500-1000 (bad), 1000- (very bad)
  public static final GradeLookupTable PMD_WARNING_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(250.0,Grade.F),
       new MarkGradePair(100.0,Grade.D),
       new MarkGradePair(50.0,Grade.C),
       new MarkGradePair(10.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );

  //PMD errors per 1000 NCSS: 0 (very good), 1-10 (good), 11-50 (ok), 50-100 (poor), 100- (poor)
  public static final GradeLookupTable PMD_ERROR_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(100.0,Grade.F),
       new MarkGradePair(50.0,Grade.D),
       new MarkGradePair(10.0,Grade.C),
       new MarkGradePair(1.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );
  
  //??
  public static final GradeLookupTable ESCJAVA2_WARNING_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(250.0,Grade.F),
       new MarkGradePair(100.0,Grade.D),
       new MarkGradePair(50.0,Grade.C),
       new MarkGradePair(10.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );

  //??
  public static final GradeLookupTable ESCJAVA2_ERROR_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(100.0,Grade.F),
       new MarkGradePair(50.0,Grade.D),
       new MarkGradePair(10.0,Grade.C),
       new MarkGradePair(1.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );
  
  //??
  public static final GradeLookupTable CHECKSTYLE_WARNING_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(1000.0,Grade.F),
       new MarkGradePair(250.0,Grade.D),
       new MarkGradePair(100.0,Grade.C),
       new MarkGradePair(25.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );

  //??
  public static final GradeLookupTable CHECKSTYLE_ERROR_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
    { new MarkGradePair(1000.0,Grade.F),
      new MarkGradePair(250.0,Grade.D),
      new MarkGradePair(100.0,Grade.C),
      new MarkGradePair(25.0,Grade.B),
      new MarkGradePair(0.0,Grade.A),
    } );
  
  //??
  public static final GradeLookupTable BONC_WARNING_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(25.0,Grade.F),
       new MarkGradePair(10.0,Grade.D),
       new MarkGradePair(4.0,Grade.C),
       new MarkGradePair(1.0,Grade.B),
       new MarkGradePair(0.0,Grade.A),
     } );

  //??
  public static final GradeLookupTable BONC_ERROR_LOOKUP 
  = new GradeLookupTable( new MarkGradePair[]
  { new MarkGradePair(25.0,Grade.F),
    new MarkGradePair(10.0,Grade.D),
    new MarkGradePair(4.0,Grade.C),
    new MarkGradePair(1.0,Grade.B),
    new MarkGradePair(0.0,Grade.A),
  } );
  
  //0-1 (poor), 2-5 (good), 5-10 (ok), 10-15 (poor), 15- (very poor)
  public static final GradeLookupTable METRICS_METHOD_LOC_LOOKUP
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(15.0,Grade.D),
       new MarkGradePair(10.0,Grade.C),
       new MarkGradePair(5.0,Grade.B),
       new MarkGradePair(2.0,Grade.A),
       new MarkGradePair(1.0,Grade.B),
       new MarkGradePair(0.0,Grade.C),
     } );
  
  // 0-0.5 (very good), 0.5-1.5 (good), 1.5-2.0 (ok), 2.0-3.0 (poor), 3.0- (very poor)
  public static final GradeLookupTable METRICS_METHOD_CC_LOOKUP
  = new GradeLookupTable( new MarkGradePair[] 
     { new MarkGradePair(3.0,Grade.D),
       new MarkGradePair(2.0,Grade.C),
       new MarkGradePair(1.5,Grade.B),
       new MarkGradePair(0.5,Grade.A),
       new MarkGradePair(0.0,Grade.A_PLUS),
     } );
  
}

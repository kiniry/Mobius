package b2bpl.bytecode;

import static b2bpl.bytecode.TroubleDescription.Kind.*;


public class B2BPLMessages {

  private B2BPLMessages() {
    // hide the constructor
  }

  public static final TroubleDescription CLASS_NOT_FOUND =
    new TroubleDescription(ERROR, "Cannot find the class ''{0}''.");

  public static final TroubleDescription UNSUPPORTED_INSTRUCTION =
    new TroubleDescription(ERROR, "The bytecode instruction ''{0}'' is not supported.");

  public static final TroubleDescription UNKNOWN_SPECIFICATION_TAG =
    new TroubleDescription(ERROR, "The BML specification tag {0} is unknown.");

  public static final TroubleDescription UNEXPECTED_SPECIFICATION_TAG =
    new TroubleDescription(ERROR, "Found the unexpected BML specification tag {0} (''{1}'').");

  public static final TroubleDescription UNEXPECTED_END_OF_BML_ATTRIBUTE =
    new TroubleDescription(ERROR, "Unexpectedly reached the end of the BML attribute.");

  public static final TroubleDescription ERROR_DURING_DATAFLOW_ANALYSIS =
    new TroubleDescription(ERROR, "An error occurred during the dataflow analysis: {0}");

  public static final TroubleDescription IRREDUCIBLE_CONTROL_FLOW_GRAPH =
    new TroubleDescription(ERROR, "The method''s control flow graph is irreducible.");
}

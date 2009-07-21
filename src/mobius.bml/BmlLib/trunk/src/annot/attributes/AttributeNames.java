package annot.attributes;


/**
 * This class contains the string which identify BML attributes.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class AttributeNames {

  /**
   * The common prefix of all the BML attribute names.
   */
  public static final String BML_DOMAIN = "org.bmlspecs.";
  /**
   * The String with the name of the Version attribute.
   */
  public static final String VERSION_ATTR = BML_DOMAIN + "Version";
  /**
   * The String with the name of the ClassModifiers attribute.
   */
  public static final String CLASS_MODIFIERS_ATTR = BML_DOMAIN +
      "ClassModifiers";
  /**
   * The String with the name of the GhostFields attribute.
   */
  public static final String GHOST_FIELDS_ATTR = BML_DOMAIN +
      "GhostFields";
  /**
   * The String with the name of the ModelFields attribute.
   */
  public static final String MODEL_FIELDS_ATTR = BML_DOMAIN +
      "ModelFields";
  /**
   * The String with the name of the ModelMethods attribute.
   */
  public static final String MODEL_METHODS_ATTR = BML_DOMAIN +
      "ModelMethods";
  /**
   * The String with the name of the Invariants attribute.
   * See section "Invariants Attribute" of "BML Reference Manual".
   */
  public static final String INVARIANTS_ATTR = BML_DOMAIN + "Invariants";
  /**
   * The String with the name of the Constraints attribute.
   */
  public static final String CONSTRAINTS_ATTR = BML_DOMAIN + "Constraints";
  /**
   * The String with the name of the InitiallyClauses attribute.
   */
  public static final String INITIALLY_CLAUSES_ATTR = BML_DOMAIN +
      "InitiallyClauses";
  /**
   * The String with the name of the RepresentsClauses attribute.
   */
  public static final String REPRESENTS_CLAUSES_ATTR = BML_DOMAIN +
      "RepresentsClauses";
  /**
   * The String with the name of the SecondConstantPool attribute.
   */
  public static final String SECOND_CONSTANT_POOL_ATTR = BML_DOMAIN +
      "SecondConstantPool";
  /**
   * The String with the name of the DataGroups attribute.
   */
  public static final String DATA_GROUPS_ATTR = BML_DOMAIN +
      "DataGroups";
  /**
   * The String with the name of the FieldModifiers attribute.
   */
  public static final String FIELD_MODIFIERS_ATTR = BML_DOMAIN +
      "FieldModifiers";
  /**
   * The String with the name of the MethodSpecificationAttribute attribute.
   */
  public static final String METHOD_SPECIFICATION_ATTR = BML_DOMAIN +
      "MethodSpecification";
  /**
   * The String with the name of the ParameterTable attribute.
   */
  public static final String PARAMETER_TABLE_ATTR = BML_DOMAIN +
      "ParameterTable";
  /**
   * The String with the name of the LocalVariableModifiersTable attribute.
   */
  public static final String LOCAL_VARIABLE_MODIFIERS_TABLE_ATTR = BML_DOMAIN +
      "LocalVariableModifiersTable";
  /**
   * The String with the name of the LocalGhostVariableTable attribute.
   */
  public static final String LOCAL_GHOST_VARIABLE_TABLE_ATTR = BML_DOMAIN +
      "LocalGhostVariableTable";
  /**
   * The String with the name of the AssertTable attribute.
   */
  public static final String ASSERT_TABLE_ATTR = BML_DOMAIN + "AssertTable";
  /**
   * The String with the name of the AssumeTable attribute.
   */
  public static final String ASSUME_TABLE_ATTR = BML_DOMAIN + "AssumeTable";
  /**
   * The String with the name of the SetTable attribute.
   */
  public static final String SET_TABLE_ATTR = BML_DOMAIN + "SetTable";
  /**
   * The String with the name of the UnreachableTable attribute.
   */
  public static final String UNREACHABLE_TABLE_ATTR = BML_DOMAIN +
      "UnreachableTable";
  /**
   * The String with the name of the LoopSpecificationTable attribute.
   */
  public static final String LOOP_SPECIFICATION_TABLE_ATTR = BML_DOMAIN +
      "LoopSpecificationTable";
  /**
   * The String with the name of the OwnershipTable attribute.
   */
  public static final String OWNERSHIP_TABLE_ATTR = BML_DOMAIN +
      "OwnershipTable";
  /**
   * The String with the name of the DebugTable attribute.
   */
  public static final String DEBUG_TABLE_ATTR = BML_DOMAIN +
      "DebugTable";
  /**
   * The array with all the BML attribute names.
   */
  public static final String[] BML_ATTRIBUTE_NAMES = {
    VERSION_ATTR,
    CLASS_MODIFIERS_ATTR,
    GHOST_FIELDS_ATTR,
    MODEL_FIELDS_ATTR,
    MODEL_METHODS_ATTR,
    INVARIANTS_ATTR,
    CONSTRAINTS_ATTR,
    INITIALLY_CLAUSES_ATTR,
    REPRESENTS_CLAUSES_ATTR,
    SECOND_CONSTANT_POOL_ATTR,
    DATA_GROUPS_ATTR,
    FIELD_MODIFIERS_ATTR,
    METHOD_SPECIFICATION_ATTR,
    PARAMETER_TABLE_ATTR,
    LOCAL_VARIABLE_MODIFIERS_TABLE_ATTR,
    LOCAL_GHOST_VARIABLE_TABLE_ATTR,
    ASSERT_TABLE_ATTR,
    ASSUME_TABLE_ATTR,
    SET_TABLE_ATTR,
    UNREACHABLE_TABLE_ATTR,
    LOOP_SPECIFICATION_TABLE_ATTR,
    OWNERSHIP_TABLE_ATTR,
    DEBUG_TABLE_ATTR
  };
  /**
   * The position of the VERSION_ATTR in
   * array of attribute names.
   */
  public static final int VERSION_ATTR_POS = 0;
  /**
   * The position of the CLASS_MODIFIERS_ATTR in
   * array of attribute names.
   */
  public static final int CLASS_MODIFIERS_ATTR_POS = 1;
  /**
   * The position of the GHOST_FIELDS_ATTR in
   * array of attribute names.
   */
  public static final int GHOST_FIELDS_ATTR_POS = 2;
  /**
   * The position of the MODEL_FIELDS_ATTR in
   * array of attribute names.
   */
  public static final int MODEL_FIELDS_ATTR_POS = 3;
  /**
   * The position of the MODEL_METHODS_ATTR in
   * array of attribute names.
   */
  public static final int MODEL_METHODS_ATTR_POS = 4;
  /**
   * The position of the INVARIANTS_ATTR in
   * array of attribute names.
   */
  public static final int INVARIANTS_ATTR_POS = 5;
  /**
   * The position of the CONSTRAINTS_ATTR in
   * array of attribute names.
   */
  public static final int CONSTRAINTS_ATTR_POS = 6;
  /**
   * The position of the INITIALLY_CLAUSES_ATTR in
   * array of attribute names.
   */
  public static final int INITIALLY_CLAUSES_ATTR_POS = 7;
  /**
   * The position of the REPRESENTS_CLAUSES_ATTR in
   * array of attribute names.
   */
  public static final int REPRESENTS_CLAUSES_ATTR_POS = 8;
  /**
   * The position of the SECOND_CONSTANT_POOL_ATTR in
   * array of attribute names.
   */
  public static final int SECOND_CONSTANT_POOL_ATTR_POS = 9;
  /**
   * The position of the DATA_GROUPS_ATTR in
   * array of attribute names.
   */
  public static final int DATA_GROUPS_ATTR_POS = 10;
  /**
   * The position of the FIELD_MODIFIERS_ATTR in
   * array of attribute names.
   */
  public static final int FIELD_MODIFIERS_ATTR_POS = 11;
  /**
   * The position of the METHOD_SPECIFICATION_ATTR in
   * array of attribute names.
   */
  public static final int METHOD_SPECIFICATION_ATTR_POS = 12;
  /**
   * The position of the PARAMETER_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int PARAMETER_TABLE_ATTR_POS = 13;
  /**
   * The position of the LOCAL_VARIABLE_MODIFIERS_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int LOCAL_VARIABLE_MODIFIERS_TABLE_ATTR_POS = 14;
  /**
   * The position of the LOCAL_GHOST_VARIABLE_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int LOCAL_GHOST_VARIABLE_TABLE_ATTR_POS = 15;
  /**
   * The position of the ASSERT_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int ASSERT_TABLE_ATTR_POS = 16;
  /**
   * The position of the ASSUME_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int ASSUME_TABLE_ATTR_POS = 17;
  /**
   * The position of the SET_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int SET_TABLE_ATTR_POS = 18;
  /**
   * The position of the UNREACHABLE_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int UNREACHABLE_TABLE_ATTR_POS = 19;
  /**
   * The position of the LOOP_SPECIFICATION_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int LOOP_SPECIFICATION_TABLE_ATTR_POS = 20;
  /**
   * The position of the OWNERSHIP_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int OWNERSHIP_TABLE_ATTR_POS = 21;
  /**
   * The position of the DEBUG_TABLE_ATTR in
   * array of attribute names.
   */
  public static final int DEBUG_TABLE_ATTR_POS = 22;

  /**
   * A private constructor to forbid the creation of instances.
   */
  private AttributeNames() {
  }

  /**
   * The method checks if the given String is a BML attribute name.
   *
   * @param aname the String to check
   * @return <code>true</code> in case the String is an attribute name,
   *   <code>false</code> otherwise.
   */
  public static boolean isBMLAttributeName(final String aname) {
    for (int i = 0; i < BML_ATTRIBUTE_NAMES.length; i++) {
      if (aname.equals(BML_ATTRIBUTE_NAMES[i])) {
        return true;
      }
    }
    return false;
  }

}

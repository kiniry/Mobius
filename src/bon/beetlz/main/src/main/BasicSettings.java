package main;

import utils.BasicTypesDictionary;

  /**
   * This class only fills in the mappings for basic types and
   * names for assertion comparison..
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
public final class BasicSettings {

  /** */
  private BasicSettings() { } 

  /**
   * Initialises basic types.
   * @param a_profile where to put settings
   */
  public static void doStuff(final UserProfile a_profile) {
    a_profile 
    .addTypeMapping("value", //$NON-NLS-1$
                    new String[]{"VALUE"}, //$NON-NLS-1$
                    new String[]{"int", "double", //$NON-NLS-1$ //$NON-NLS-2$
                                 "short", "long", //$NON-NLS-1$ //$NON-NLS-2$
                                 "float", "byte", //$NON-NLS-1$ //$NON-NLS-2$
                                 "AtomicInteger", "AtomicLong", //$NON-NLS-1$ //$NON-NLS-2$
                                 "BigDecimal", "BigInteger", //$NON-NLS-1$ //$NON-NLS-2$
                                 "Byte", "Double", //$NON-NLS-1$ //$NON-NLS-2$
                                 "Float", //$NON-NLS-1$
                                 "Long", "Short", //$NON-NLS-1$ //$NON-NLS-2$
                                 "Number", "Integer", //$NON-NLS-1$ //$NON-NLS-2$
                                 "boolean", "Boolean", //$NON-NLS-1$ //$NON-NLS-2$
                                 "char", //$NON-NLS-1$
                                 "Character", "String" }); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile
    .addTypeMapping("numeric", //$NON-NLS-1$
                    new String[] {"NUMERIC"}, //$NON-NLS-1$
                    new String[] {"int", "double", //$NON-NLS-1$ //$NON-NLS-2$
                                  "short", "long", //$NON-NLS-1$ //$NON-NLS-2$
                                  "float", "byte", //$NON-NLS-1$ //$NON-NLS-2$
                                  "AtomicInteger", "AtomicLong", //$NON-NLS-1$ //$NON-NLS-2$
                                  "BigDecimal", "BigInteger", //$NON-NLS-1$ //$NON-NLS-2$
                                  "Byte", "Double", //$NON-NLS-1$ //$NON-NLS-2$
                                  "Float", //$NON-NLS-1$
                                  "Long", "Short", //$NON-NLS-1$ //$NON-NLS-2$
                                  "Number", "Integer" }); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile
    .addTypeMapping("integer", //$NON-NLS-1$
                    new String[] {"INTEGER"}, //$NON-NLS-1$
                    new String[] {"int", "long", //$NON-NLS-1$ //$NON-NLS-2$
                                  "short", "byte", //$NON-NLS-1$ //$NON-NLS-2$
                                  "AtomicInteger", "AtomicLong", //$NON-NLS-1$ //$NON-NLS-2$
                                  "BigInteger", //$NON-NLS-1$
                                  "Byte", "Short", //$NON-NLS-1$ //$NON-NLS-2$
                                  "Long", "Integer" }); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile.addTypeMapping("real", //$NON-NLS-1$
                             new String[] {"REAL"}, //$NON-NLS-1$
                             new String[] {"double", "float", //$NON-NLS-1$ //$NON-NLS-2$
                                           "BigDecimal", //$NON-NLS-1$
                                           "Float", "Double" }); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile.addTypeMapping("boolean", //$NON-NLS-1$
                             new String[] {"BOOLEAN"}, //$NON-NLS-1$
                             new String[] {"boolean", "Boolean"}); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile.addTypeMapping("character", //$NON-NLS-1$
                             new String[] {"CHARACTER"}, //$NON-NLS-1$
                             new String[] {"char", "Character" }); //$NON-NLS-1$ //$NON-NLS-2$
    a_profile.addTypeMapping("string", //$NON-NLS-1$
                             new String[] {"STRING"}, //$NON-NLS-1$
                             new String[] {"String"}); //$NON-NLS-1$
    a_profile.addTypeMapping("object", //$NON-NLS-1$
                             new String[] {"ANY"}, //$NON-NLS-1$
                             new String[] {"Object"}); //$NON-NLS-1$
    a_profile.addTypeMapping("set", //$NON-NLS-1$
                             new String[] {"SET"}, //$NON-NLS-1$
                             new String[] {"Set", "HashSet", //$NON-NLS-1$ //$NON-NLS-2$
                                           "TreeSet", //$NON-NLS-1$
                                           "SortedSet", //$NON-NLS-1$
                                           "NavigableSet", //$NON-NLS-1$
                                           "ConcurrentSkipListSet", //$NON-NLS-1$
                                           "AbstractSet", //$NON-NLS-1$
                                           "CopyOnWriteArraySet", //$NON-NLS-1$
                                           "EnumSet", //$NON-NLS-1$
                                           "LinkedHashSet" }); //$NON-NLS-1$
    a_profile
    .addTypeMapping("sequence", //$NON-NLS-1$
                    new String[] {"SEQUENCE"}, //$NON-NLS-1$
                    new String[] {"List", "Vector", //$NON-NLS-1$ //$NON-NLS-2$
                                  "Array", //$NON-NLS-1$
                                  "AbstractList", //$NON-NLS-1$
                                  "AbstractSequentialList", //$NON-NLS-1$
                                  "ArrayList", //$NON-NLS-1$
                                  "AttributeList", //$NON-NLS-1$
                                  "CopyOnWriteArrayList", //$NON-NLS-1$
                                  "LinkedList", //$NON-NLS-1$
                                  "RoleList", //$NON-NLS-1$
                                  "RoleUnresolvedList", //$NON-NLS-1$
                                  "Stack", //$NON-NLS-1$
                                  "Aray", //$NON-NLS-1$
                                  "Queue", "AbstractQueue", //$NON-NLS-1$ //$NON-NLS-2$
                                  "ArrayBlockingQueue", //$NON-NLS-1$
                                  "ArrayDeque", //$NON-NLS-1$
                                  "ConcurrentLinkedQueue", //$NON-NLS-1$
                                  "DelayQueue", //$NON-NLS-1$
                                  "LinkedBlockingDeque", //$NON-NLS-1$
                                  "LinkedBlockingQueue", //$NON-NLS-1$
                                  "LinkedList", //$NON-NLS-1$
                                  "PriorityBlockingQueue", //$NON-NLS-1$
                                  "PriorityQueue", //$NON-NLS-1$
                                  "SynchronousQueue", //$NON-NLS-1$
                                  "Deque", //$NON-NLS-1$
                                  "BlockingQueue", //$NON-NLS-1$
                                  "BlockingDeque" }); //$NON-NLS-1$
    a_profile.addTypeMapping("table", //$NON-NLS-1$
                             new String[] {"TABLE"}, //$NON-NLS-1$
                             new String[] {"Map", "HashMap", //$NON-NLS-1$ //$NON-NLS-2$
                                           "AbstractMap", //$NON-NLS-1$
                                           "Attributes", //$NON-NLS-1$
                                           "AuthProvider", //$NON-NLS-1$
                                           "ConcurrentHashMap", //$NON-NLS-1$
                                           "ConcurrentSkipListMap", //$NON-NLS-1$
                                           "EnumMap", //$NON-NLS-1$
                                           "Hashtable", //$NON-NLS-1$
                                           "IdentityHashMap", //$NON-NLS-1$
                                           "LinkedHashMap", //$NON-NLS-1$
                                           "PrinterStateReasons", //$NON-NLS-1$
                                           "Properties", //$NON-NLS-1$
                                           "Provider", //$NON-NLS-1$
                                           "RenderingHints", //$NON-NLS-1$
                                           "SimpleBindings", //$NON-NLS-1$
                                           "TabularDataSupport", //$NON-NLS-1$
                                           "TreeMap", //$NON-NLS-1$
                                           "UIDefaults", //$NON-NLS-1$
                                           "WeakHashMap", //$NON-NLS-1$
                                           "Bindings", //$NON-NLS-1$
                                           "ConcurrentMap", //$NON-NLS-1$
                                           "ConcurrentNavigableMap", //$NON-NLS-1$
                                           "LogicalMessageContext", //$NON-NLS-1$
                                           "MessageContext", //$NON-NLS-1$
                                           "NavigableMap", //$NON-NLS-1$
                                           "SOAPMessageContext", //$NON-NLS-1$
                                           "SortedMap"}); //$NON-NLS-1$
    a_profile.addSimpleFeatureMapping("length", "size"); //$NON-NLS-1$ //$NON-NLS-2$

  }

  /**
   * Initialises assertion basic settings.
   * @param a_dict where to put stuff
   */
  public static void doAssertionStuff(final BasicTypesDictionary a_dict) {
    a_dict.addMapping("empty", //$NON-NLS-1$
                    new String[] {"empty"}, //$NON-NLS-1$
                    new String[] {"isEmpty"}); //$NON-NLS-1$
    a_dict
        .addMapping(
                    "length", new String[] {"count"}, //$NON-NLS-1$ //$NON-NLS-2$
                    new String[] {"length", "size"}); //$NON-NLS-1$ //$NON-NLS-2$
    a_dict.addMapping("item", new String[] {"item"}, //$NON-NLS-1$ //$NON-NLS-2$
                    new String[] {"get"}); //$NON-NLS-1$

  }
}

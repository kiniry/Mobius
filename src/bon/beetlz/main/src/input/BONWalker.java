package input;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.BONST;

import java.util.HashMap;
import java.util.Map;

import main.Beetlz;
import main.UserProfile;
import structure.ClassStructure;
import utils.smart.TypeSmartString;

/**
 * Initialises parsing of BON classes from TypingInformation from BONc.
 * Additionally it takes of correctly assigning client relations.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 *
 */
public class BONWalker {
  /** Access the classes by their name. */
  private final Map < String, ClassStructure > my_classes;

  /**
   * Create a new BON walker.
   */
  public BONWalker() {
    this.my_classes = new HashMap < String, ClassStructure > ();
  }

  /**
   * Parse info.
   * @param the_tracker parse information
   */
  public final void parseTypingInformation(final ParsingTracker the_tracker) {
    final UserProfile profile = Beetlz.getProfile();
    final BONST the_st = the_tracker.getSymbolTable();
    
    final Map<String,Cluster> clusterList = the_st.classClusterMap;

    for (final Clazz c : the_st.classes.values()) {
      if (!profile.isBONIgnored(c.name.name)) {
        Cluster clusterInfo = clusterList.get(c.name.name);
        final ClassStructure temp = BONParser.parseClass(the_st, c, clusterInfo);
        my_classes.put(temp.getSimpleName(), temp);
      }
    }

    
    for (final ClientRelation cr : the_st.clientRelations) {
      if (my_classes.containsKey(cr.getClient().getName().getName()) && 
          my_classes.containsKey(cr.getSupplier().getName().getName())) {
        if (cr.typeMark.mark == TypeMark.Mark.AGGREGATE) {
          my_classes.get(cr.getClient().getName().getName()).
            addAggregation(new TypeSmartString(my_classes.
                                             get(cr.getSupplier().getName().getName()).
                                             getSimpleName()));
        }
        if (cr.typeMark.mark == TypeMark.Mark.SHAREDMARK) {
          my_classes.get(cr.getClient().getName().getName()).
            addSharedAssociation(new TypeSmartString(cr.supplier.name.name));
        }
      }
    }
  }

  /**
   * Get classes.
   * @return map with classes.
   */
  public final Map < String, ClassStructure > getAllClasses() {
    return my_classes;
  }

}


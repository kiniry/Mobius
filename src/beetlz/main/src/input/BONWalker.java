package input;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import main.Beetlz;
import main.UserProfile;

import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.typechecker.ClassDefinition;
import ie.ucd.bon.typechecker.ClientRelation;
import ie.ucd.bon.typechecker.ClusterDefinition;
import ie.ucd.bon.typechecker.TypingInformation;
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
   * @param the_info typing information
   */
  public final void parseTypingInformation(final TypingInformation the_info) {
    final Graph < String, ClusterDefinition > clusterList = the_info.getClassClusterGraph();
    final UserProfile profile = Beetlz.getProfile();

    for (final ClassDefinition c : the_info.getClasses().values()) {
      if (!profile.isBONIgnored(c.getName())) {
        final Set < ClusterDefinition > clusterInfo = clusterList.getLinkedNodes(c.getName());
        final ClassStructure temp = BONParser.parseClass(c, clusterInfo);
        my_classes.put(temp.getSimpleName(), temp);
      }
    }

    for (final ClientRelation cr : the_info.getClientRelations()) {
      if (my_classes.containsKey(cr.getClient()) && my_classes.containsKey(cr.getSupplier())) {
        if (cr.getTypeMark().isAggregate()) {
          my_classes.get(cr.getClient()).
            addAggregation(new TypeSmartString(my_classes.
                                             get(cr.getSupplier()).
                                             getSimpleName()));
        }
        if (cr.getTypeMark().isSharedMark()) {
          my_classes.get(cr.getClient()).
            addSharedAssociation(new TypeSmartString(cr.getSupplier()));
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


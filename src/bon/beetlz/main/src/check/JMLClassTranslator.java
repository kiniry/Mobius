package check;

import java.util.List;
import java.util.Vector;

import log.CCLogManager;
import logic.Expression;
import main.Beetlz;
import main.UserProfile;
import structure.ClassStructure;
import structure.FeatureStructure;
import structure.Invariant;
import utils.BeetlzSourceLocation;
import utils.ModifierManager.ClassType;
import utils.smart.SmartString;

/**
 * Compare jml class assrtions.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class JMLClassTranslator {

  /** The source feature's name.  */
  private ClassStructure my_srcCls;
  /**  The target feature's name. */
  private ClassStructure my_trgCls;
  /**  The target class's name. */
  private SmartString my_trgName;
  /** Source location  of target feature (shortcut).*/
  private BeetlzSourceLocation my_src;
  /** Logger for this session.  */
  private final CCLogManager my_logger;
  /** User settings.  */
  private final UserProfile my_profile;


  /**
   * Creates a new JMLTranslator.
   * @param a_log Logger for error messages
   * @param a_profile user settings
   */
  public JMLClassTranslator(final CCLogManager a_log, final UserProfile a_profile) {
    my_logger = a_log;
    my_profile = a_profile;
  }

  /**
   * Do the actual checking of two features.
   * Note, no check is performed that they actually are from two different
   * sources, ie no check that one is BON and the other is Java.
   * @param a_src_cls source feature
   * @param a_trg_cls target feature
   * @param a_src source location
   * @return success rate
   */
  public double doCheck(final ClassStructure a_src_cls,
                        final ClassStructure a_trg_cls,
                        final BeetlzSourceLocation a_src) {
    my_srcCls = a_src_cls;
    my_trgCls = a_trg_cls;
    my_trgName = my_trgCls.getName();
    my_src = a_src;
    double success = 0;
    success += relateInvariants();
    if (my_srcCls.getType() == ClassType.JAVA && !Beetlz.getProfile().pureBon()) {
      success += relateHistoryConstraints();
    }


    return success; //some score...
  }

  /**
   * Relate invariant.
   * @return success value
   */
  private double relateInvariants() {
    double success = 1;
    final Invariant srcInv = my_srcCls.getInvariant();
    final Invariant trgInv = my_trgCls.getInvariant();
    if (srcInv != null && trgInv == null) {
      my_logger.logMissingInvariant(my_src, my_trgName);
    } else if (srcInv != null && trgInv != null) {
      final List < Expression > srcCond = srcInv.getNonTrivialPredicates();
      final List < Expression > trgCond = trgInv.getNonTrivialPredicates();

      for (int i = 0; i < trgCond.size(); i++) {
        for (int j = 0; j < srcCond.size(); j++) {
          final Expression src = srcCond.get(j);
          final Expression trg = trgCond.get(i);
          if (trg.compareToTyped(src) == 0) {
            trgCond.remove(i);
            srcCond.remove(j);
            i--;
            j = srcCond.size();
          }
        }
      }

      //Case: more args in BON, i.e. args missing
      if (srcCond.size() > 0) {
        my_logger.logMissingInvariantClauses(my_src, my_trgCls.getName(),
                                             srcCond);
        success = 0;
      }
      //Case: more args in Java, i.e. args too much
      if (trgCond.size() > 0 && my_profile.javaIsSource()) {
        my_logger.logTooManyInvariant(my_src, my_trgCls.getName(), trgCond);
        success = 0;
      }

    }
    return success;

  }

  /**
   * Relate history constraints.
   * @return success value
   */
  private double relateHistoryConstraints() {
    final double success = 1;
    final List < Expression > history =
      new Vector < Expression > (my_srcCls.getInvariant().getHistoryConstraints());
    if (history.size() > 0) my_logger.logHistoryConstraints();

    for (final Expression e : history) {
      boolean found = false;
      for (final FeatureStructure feat : my_trgCls.getFeatures()) {
        if (!feat.getSpec().isEmpty()) {
          for (final Expression post : feat.getSpec().get(0).getPostconditions()) {
            if (post.compareToTyped(e) == 0) {
              found = true;
              continue;
            }
          }
        }
      }
      for (final FeatureStructure feat : my_trgCls.getConstructors()) {
        if (!feat.getSpec().isEmpty()) {
          for (final Expression post : feat.getSpec().get(0).getPostconditions()) {
            if (post.compareToTyped(e) == 0) {
              found = true;
              continue;
            }
          }
        }
      }
      if (!found)    my_logger.logMissingHistoryContraint(my_src, my_trgName, e);
    }
    return success;
  }

}

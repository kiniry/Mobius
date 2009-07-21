package check;

import java.util.List;
import java.util.SortedSet;
import java.util.Vector;

import log.CCLogManager;
import logic.Expression;
import logic.Expression.Nullity;
import main.Beetlz;
import main.UserProfile;
import structure.ClassStructure;
import structure.FeatureStructure;
import structure.Spec;
import utils.BConst;
import utils.Helper;
import utils.SourceLocation;
import utils.smart.FeatureSmartString;
import utils.smart.SmartString;

/**
 * Compare JML on features.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class JMLFeatureTranslator {

  /** The source feature's name.  */
  private FeatureStructure my_srcFeat;
  /**  The target feature's name. */
  private FeatureStructure my_trgFeat;
  /** The source feature's name.  */
  private ClassStructure my_srcCls;
  /**  The target feature's name. */
  private ClassStructure my_trgCls;
  /**  The target feature's name. */
  private SmartString my_trgName;
  /** The source feature.  */
  private Spec my_srcSpec;
  /**  The target features.  */
  private Spec my_trgSpec;
  /** Source location  of target feature (shortcut).*/
  private SourceLocation my_src;
  /** Logger for this session.  */
  private final CCLogManager my_logger;
  /** User settings.  */
  private final UserProfile my_profile;

  //private SortedSet < ClassStructure > assignable


  /**
   * Creates a new JMLTranslator.
   * @param a_log Logger for error messages
   * @param a_profile user settings
   */
  public JMLFeatureTranslator(final CCLogManager a_log, final UserProfile a_profile) {
    my_logger = a_log;
    my_profile = a_profile;
  }

  /**
   * Do a check.
   * @param a_src_spec source specs
   * @param a_src_name source feature name
   * @param a_trg_spec target specs
   * @param a_trg_name target feature name
   * @param a_src source location of target
   * @return success value
   */
  public double doCheck(final Spec a_src_spec, final FeatureStructure a_src_name,
                        final Spec a_trg_spec, final FeatureStructure a_trg_name,
                        final SourceLocation a_src) {
    my_srcSpec = a_src_spec;
    my_trgSpec = a_trg_spec;
    my_srcFeat = a_src_name;
    my_trgFeat = a_trg_name;
    my_srcCls = my_srcFeat.getEnclosingClass();
    my_trgCls = my_trgFeat.getEnclosingClass();
    my_trgName = my_trgFeat.getName();

    my_src = a_src;
    double success = 0;

    //Check: does the enclosing class contain any assignable clauses?
    //If not then we just issue ONE warning and not LOADS:
    if (my_srcCls.usesAssignable() || my_trgCls.usesAssignable()) {
      success += relateAssignable();
    } else {
      my_logger.logAssignableDefaultCorrespondence();
    }
    if (my_profile.nullity() && (my_srcCls.usesNullity() || my_trgCls.usesNullity())) {
      success += relateNullity();
    } else if (my_profile.nullity()) {
      my_logger.logNullityDefaultCorrespondence();
    }

    success += relateType();
    success += relatePrecondition();
    success += relatePostcondition();


    return success; //some score...
  }


  /**
   * Relate assignable clause.
   * @return return value.
   */
  private double relateAssignable() {
    final double success = 1;
    final SortedSet < FeatureSmartString > trgFrame = my_trgSpec.getFrame();
    final SortedSet < FeatureSmartString > srcFrame = my_srcSpec.getFrame();
    if (srcFrame.contains(FeatureSmartString.everything()) &&
        trgFrame.contains(FeatureSmartString.nothing())) {
      my_logger.logIncorrectFrameDefault(my_src, my_trgCls.getName(), my_trgName,
                                         BConst.EVERYTHING, BConst.NOTHING);
    } else if (srcFrame.contains(FeatureSmartString.nothing()) &&
        trgFrame.contains(FeatureSmartString.everything())) {
      my_logger.logIncorrectFrameDefault(my_src, my_trgCls.getName(), my_trgName,
                                         BConst.NOTHING, BConst.EVERYTHING);
    } else if (srcFrame.contains(FeatureSmartString.everything())) {
      if (!trgFrame.contains(FeatureSmartString.everything())) {
        my_logger.logIncorrectFrameCondition(my_src, my_trgCls.getName(), my_trgName,
                                             BConst.EVERYTHING, trgFrame.toString());
      }
    } else if (srcFrame.size() == 1 && srcFrame.first().equals(FeatureSmartString.nothing())) {
      if (!trgFrame.contains(FeatureSmartString.nothing())) {
        my_logger.logIncorrectFrameCondition(my_src, my_trgCls.getName(), my_trgName,
                                             BConst.NOTHING, trgFrame.toString());
      }
    } else {
      for (final FeatureSmartString s : my_srcSpec.getFrame()) {
        if (!Helper.containsTyped(trgFrame, s)) {
          final String map = my_profile.getFeatureMapping(s.toString(),
                                                          my_srcCls.getQualifiedName().
                                                          toString(),
                                                          my_trgCls.getSimpleName());
          if (map == null || !trgFrame.contains(new SmartString(map))) {
            my_logger.logMissingFrameCondition(my_src, my_trgCls.getName(),  my_trgName, s);
          }
        }
      }
    }


    return success;
  }

  /**
   * Check feature types: command, query, hybrid.
   * @return value between 0 - 1, 1 being equal
   */
  private double relateType() {
    double success = 0;
    if (my_srcFeat.getFeatureType() != my_trgFeat.getFeatureType()) {
      my_logger.logIncorrectFeatureType(my_src, my_trgCls.getName(), my_trgName,
                                        my_srcFeat.getFeatureType(),
                                        my_trgFeat.getFeatureType());
      success = 0;
    }
    return success;
  }


  /**
   * Check preconditions.
   * @return value between 0 - 1, 1 being equal
   */
  private double relatePrecondition() {
    double success = 1;
    final List < Expression > srcCond = my_srcSpec.getNonTrivialPreconditions();
    final List < Expression > trgCond = my_trgSpec.getNonTrivialPreconditions();

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
      my_logger.logMissingPrecondition(my_src, my_trgCls.getName(), my_trgName, srcCond);
      success = 0;
    }
    //Case: more args in Java, i.e. args too much
    if (trgCond.size() > 0 && my_profile.javaIsSource()) {
      my_logger.logTooManyPrecondition(my_src, my_trgCls.getName(), my_trgName, trgCond);
      success = 0;
    }

    return success;
  }

  /**
   * Check postconditions.
   * @return value between 0 - 1, 1 being equal
   */
  private double relatePostcondition() {
    double success = 1;
    final List < Expression > srcCond = my_srcSpec.getNonTrivialPostconditions();
    final List < Expression > trgCond = my_trgSpec.getNonTrivialPostconditions();
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
    //Check if we can find some of the missing ones in the history constraints
    if (!Beetlz.getProfile().pureBon()) {
      List < Expression > history =
        new Vector < Expression > (my_trgCls.getInvariant().getHistoryConstraints());
      for (int j = 0; j < srcCond.size(); j++) {
        for (int i = 0; i < history.size(); i++) {
          if (history.get(i).compareToTyped(srcCond.get(j)) == 0) {
            srcCond.remove(j);
          }
        }
      }

      history = new Vector < Expression > (my_srcCls.getInvariant().getHistoryConstraints());
      for (int j = 0; j < trgCond.size(); j++) {
        for (int i = 0; i < history.size(); i++) {
          if (history.get(i).compareToTyped(trgCond.get(j)) == 0) {
            trgCond.remove(j);
          }
        }
      }
    }

    //Case: more args in BON, i.e. args missing
    if (srcCond.size() > 0) {
      my_logger.logMissingPostcondition(my_src, my_trgCls.getName(), my_trgName, srcCond);
      success = 0;
    }
    //Case: more args in Java, i.e. args too much
    if (trgCond.size() > 0 && my_profile.javaIsSource()) {
      my_logger.logTooManyPostcondition(my_src, my_trgCls.getName(), my_trgName, trgCond);
      success = 0;
    }

    return success;
  }

  /**
   * Relate nullity.
   * @return success value
   */
  private double relateNullity() {
    double success = 1;
    final SmartString srcType = my_srcFeat.getSignature().getReturnValue();
    final SmartString trgType = my_trgFeat.getSignature().getReturnValue();
    if (!(srcType.equals(SmartString.getVoid()) ||
        trgType.equals(SmartString.getVoid()))) {
      if (srcType.getNullity() != trgType.getNullity()) {
        success = 0;
        my_logger.logIncorrectReturnTypeNullity(my_src, my_trgCls.getName(),
                                                my_trgName, srcType.getNullity(),
                                                trgType.getNullity());
      }
    }
    int src_nullable = 0; int src_nonnull = 0;
    int trg_nullable = 0; int trg_nonnull = 0;
    for (final SmartString s : my_srcFeat.getSignature().getFormalTypes()) {
      if (s.getNullity() != null && s.getNullity() == Nullity.NON_NULL) {
        src_nonnull++;
      }
      if (s.getNullity() != null && s.getNullity() == Nullity.NULLABLE) {
        src_nullable++;
      }
    }
    for (final SmartString s : my_trgFeat.getSignature().getFormalTypes()) {
      if (s.getNullity() != null && s.getNullity() == Nullity.NON_NULL) {
        trg_nonnull++;
      }
      if (s.getNullity() != null && s.getNullity() == Nullity.NULLABLE) {
        trg_nullable++;
      }
    }
    if (src_nullable != trg_nullable || src_nonnull != trg_nonnull) {
      my_logger.logIncorrectParameterTypeNullity(my_src, my_trgCls.getName(), my_trgName);
    }

    return success;

  }

}

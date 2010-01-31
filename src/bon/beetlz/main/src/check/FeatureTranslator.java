/**
 * Package for consistency check.
 */
package check;


import java.util.List;
import java.util.SortedSet;
import java.util.Vector;

import log.CCLogManager;
import main.UserProfile;
import structure.FeatureStructure;
import utils.BasicTypesDictionary;
import utils.Helper;
import utils.BeetlzSourceLocation;
import utils.ModifierManager.FeatureModifier;
import utils.smart.SmartString;

/**
 * Compares two features for consistency.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class FeatureTranslator {
  /** The source feature's name.  */
  private SmartString my_src_name;
  /**  The target feature's name. */
  private SmartString my_trg_name;
  /** The source feature.  */
  private FeatureStructure my_src_feature;
  /**  The target features.  */
  private FeatureStructure my_trg_feature;
  /** The enclosing class of the source feature.  */
  private SmartString my_src_cls_name;
  /** The enclosing class of the target feature.  */
  private SmartString my_trg_cls_name;
  /** Source location  of target feature (shortcut).*/
  private BeetlzSourceLocation my_src;
  /** Basic types dictionary.  */
  private BasicTypesDictionary my_basic_types;
  /** Logger for this session.  */
  private CCLogManager my_logger;
  /** User settings.  */
  private UserProfile my_profile;

  /**
   * Creates a new FeatureTranslator.
   * @param a_log Logger for error messages
   * @param a_profile user settings
   */
  public FeatureTranslator(final CCLogManager a_log, final UserProfile a_profile) { 
    my_logger = a_log;
    my_profile = a_profile;
    my_basic_types = my_profile.getBasicDictionary();
  }

  /**
   * Do the actual checking of two features.
   * Note, no check is performed that they actually are from two different
   * sources, ie no check that one is BON and the other is Java.
   * @param a_src_feature source feature
   * @param a_trg_feature target feature
   * @return success rate
   */
  public double doCheck(final FeatureStructure a_src_feature,
                        final FeatureStructure a_trg_feature) {
    my_src_feature = a_src_feature;
    my_trg_feature = a_trg_feature;
    my_src_name = my_src_feature.getName();
    my_trg_name = my_trg_feature.getName();

    my_src = my_trg_feature.getSourceLoc();
    my_src_cls_name = my_src_feature.getEnclosingClass().getName();
    my_trg_cls_name = my_trg_feature.getEnclosingClass().getName();

    double success = 0;
    success += relateVisibility();
    success += relateModifier();
    success += relateReturnValue();
    success += relateParameter();
    success += relateGenerics();
    if (!my_profile.noJml()) {
      success += relateSpecs();
    }

    return success; //some score...
  }

  /**
   * Quick check whether two features may be equal.
   * @param a_src_feature source feature
   * @param a_trg_feature target feature
   * @return success value
   */
  public double doQuickCheck(final FeatureStructure a_src_feature,
                             final FeatureStructure a_trg_feature) {
    my_src_feature = a_src_feature;
    my_trg_feature = a_trg_feature;
    my_src_name = my_src_feature.getName();
    my_trg_name = my_trg_feature.getName();

    my_src = my_trg_feature.getSourceLoc();
    my_src_cls_name = my_src_feature.getEnclosingClass().getName();
    my_trg_cls_name = my_trg_feature.getEnclosingClass().getName();

    double success = 1;

    final List < SmartString > srcArgs =
      new Vector < SmartString > (my_src_feature.getSignature().getFormalTypes());
    final List < SmartString > trgArgs =
      new Vector < SmartString > (my_trg_feature.getSignature().getFormalTypes());

    for (int i = 0; i < trgArgs.size(); i++) {
      for (int j = 0; j < srcArgs.size(); j++) {
        final SmartString src = srcArgs.get(j);
        final SmartString trg = trgArgs.get(i);
        if (trg.equalsTyped(src) ||
            my_basic_types.matchTypes(trg, src)) {
          trgArgs.remove(i);
          srcArgs.remove(j);
          i--;
          j = srcArgs.size();
        } else if (Helper.isGenericsDummy(src.toString(), my_src_feature) &&
            Helper.isGenericsDummy(trg.toString(), my_trg_feature)) {
          trgArgs.remove(i);
          srcArgs.remove(j);
          i--;
          j = srcArgs.size();
        }
      }
    }
    //Case: more args in BON, i.e. args missing
    if (srcArgs.size() > 0) {
      success = 0;
    }
    //Case: more args in Java, i.e. args too much
    if (trgArgs.size() > 0) {
      success = 0;
    }

    return success; //some score...
  }

  /**
   * Check visibility modifier and restrictions.
   * @return success value
   */
  private double relateVisibility() {
    double success = 1;
    if (my_src_feature.getVisibility() != my_trg_feature.getVisibility()) {
      my_logger.logIncorrectVisibilityModifier(my_src, my_trg_cls_name, my_trg_name,
                                               my_src_feature.getVisibility(),
                                               my_trg_feature.getVisibility());
      success = 0;
    }

    return success;
  }

  /**
   * Check other modifiers.
   * @return success value
   */
  private double relateModifier() {
    double success = 1;
    //Common procedure:
    final SortedSet < FeatureModifier > srcMods = my_src_feature.getModifiers();
    //-------REDEFINED (@Override) --------
    if (my_src_feature.isRedefined()) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      } else if (!my_trg_feature.isRedefined()) {
        my_logger.logExpectedFeatureModifierWarning(my_src, my_trg_cls_name,
                                                    my_trg_name, FeatureModifier.REDEFINED);
        success = 0;
      }
    } else {
      if (my_trg_feature.isRedefined()) {
        my_logger.logShouldNotFeatureModifierWarning(my_src, my_trg_cls_name,
                                                     my_trg_name, FeatureModifier.REDEFINED);
        success = 0;
      }
    }

    if (my_src_feature.isConstant()) {
      if (!my_trg_feature.isConstant()) {
        my_logger.logExpectedFeatureModifier(my_src, my_trg_cls_name, my_trg_name,
                                             FeatureModifier.CONSTANT);
      }
    //-------ABSTRACT--------
    } else if (my_src_feature.isAbstract()) {
      if (!my_trg_feature.isAbstract() && !my_trg_feature.isConstant()) {

        if ((my_trg_feature.isRedefined())) {
          my_logger.logRedefinedCorrespondence(my_src, my_trg_cls_name, my_trg_name);
        }
        my_logger.logExpectedFeatureModifier(my_src, my_trg_cls_name, my_trg_name,
                                             FeatureModifier.ABSTRACT);
        success = 0;
      }
    }

    if (srcMods.size() == 0) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      }
    }

    //Now do the rest:
    if (my_profile.javaIsSource()) {
      success = relateJavaToBonModifier();
    } else {
      success = relateBonToJavaModifier();
    }
    return success;
  }

  /**
   * Check modifier with Java -> BON direction.
   * @return success value
   */
  private double relateJavaToBonModifier() {
    double success = 1;
    //We ignore the modifier: strictfp, synchronized, transient, volatile
    final SortedSet < FeatureModifier > jMods = my_src_feature.getModifiers();

    //-------FINAL--------
    if (my_src_feature.isFinal()) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      }
    }

    //-------NATIVE--------
    if (jMods.contains(FeatureModifier.NATIVE)) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      }
    }
    //-------STATIC--------
    if (jMods.contains(FeatureModifier.STATIC)) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      }
    }
    return success;
  }

  /**
   * Check modifier with BON -> Java direction.
   * @return success value
   */
  private double relateBonToJavaModifier() {
    double success = 1;
    final SortedSet < FeatureModifier > bMods = my_src_feature.getModifiers();
    //-------EFFECTIVE--------
    if (bMods.contains(FeatureModifier.EFFECTIVE)) {
      if (my_trg_feature.isAbstract()) {
        my_logger.logIncorrectModifier(my_src, my_trg_cls_name, my_trg_name,
                                       FeatureModifier.IMPLEMENTED, FeatureModifier.ABSTRACT);
        success = 0;
      }
    }
    return success;
  }

  /**
   * Relate generics.
   * @return success value
   */
  private double relateGenerics() {
    final double success = 1;
    if (my_src_feature.getGenerics().size() > 0) {
      my_logger.logGenericMethodNotSupported(my_src, my_src_cls_name, my_src_name);
    } else if (my_trg_feature.getGenerics().size() > 0) {
      my_logger.logGenericMethodNotSupported(my_src, my_trg_cls_name, my_trg_name);
    }
    return success;
  }

  /**
   * Check return values.
   * @return success value
   */
  private double relateReturnValue() {
    double success = 1;
    final SmartString srcType = my_src_feature.getSignature().getReturnValue();
    final SmartString trgType = my_trg_feature.getSignature().getReturnValue();
    
    if (!(srcType.equalsTyped(trgType) ||
        my_basic_types.matchTypes(srcType, trgType))) {
      if (!(Helper.isGenericsDummy(srcType.toString(), my_src_feature) &&
          Helper.isGenericsDummy(trgType.toString(), my_trg_feature))) {
        my_logger.logIncorrectReturnType(my_src, my_trg_cls_name,
                                         my_trg_name, srcType, trgType);
        success = 0;
      }
    }
    return success;
  }

  /**
   * Check formal parameter.
   * @return success value
   */
  private double relateParameter() {
    double success = 1;
    final List < SmartString > srcArgs =
      new Vector < SmartString > (my_src_feature.getSignature().getFormalTypes());
    final List < SmartString > trgArgs =
      new Vector < SmartString > (my_trg_feature.getSignature().getFormalTypes());

    for (int i = 0; i < trgArgs.size(); i++) {
      for (int j = 0; j < srcArgs.size(); j++) {
        final SmartString src = srcArgs.get(j);
        final SmartString trg = trgArgs.get(i);
        if (trg.equalsTyped(src) ||
            my_basic_types.matchTypes(trg, src)) {
          trgArgs.remove(i);
          srcArgs.remove(j);
          i--;
          j = srcArgs.size();
        } else if (Helper.isGenericsDummy(src.toString(), my_src_feature) &&
            Helper.isGenericsDummy(trg.toString(), my_trg_feature)) {
          trgArgs.remove(i);
          srcArgs.remove(j);
          i--;
          j = srcArgs.size();
        }
      }
    }
    //Case: more args in BON, i.e. args missing
    if (srcArgs.size() > 0) {
      my_logger.logMissingParameter(my_src, my_trg_cls_name, my_trg_name, srcArgs);
      success = 0;
    }
    //Case: more args in Java, i.e. args too much
    if (trgArgs.size() > 0) {
      my_logger.logTooManyParameter(my_src, my_trg_cls_name, my_trg_name, trgArgs);
      success = 0;
    }
    return success;
  }

  /**
   * Relate specs.
   * @return success value
   */
  private  double relateSpecs() {
    final double success = 1;
    final JMLFeatureTranslator jml = new JMLFeatureTranslator(my_logger, my_profile);
    if (!my_src_feature.getSpec().isEmpty() && !my_trg_feature.getSpec().isEmpty()) {
      jml.doCheck(my_src_feature.getSpec().get(0), my_src_feature,
                  my_trg_feature.getSpec().get(0), my_trg_feature,
                  my_src);
    }
    return success;
  }

}



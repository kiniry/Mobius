/** Package for consistency checker. */
package check;

import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.SortedSet;
import java.util.Vector;

import log.CCLogManager;
import main.Beetlz;
import main.UserProfile;
import structure.ClassStructure;
import structure.FeatureStructure;
import utils.BConst;
import utils.BeetlzSourceLocation;
import utils.Helper;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.ClassType;
import utils.smart.SmartString;

/**
 * Compares a source and a target class for consistency.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ClassTranslator {
  /**  Target class name.  */
  private SmartString my_trg_name;
  /**  Source class.  */
  private ClassStructure my_src_class;
  /**  Target class.  */
  private ClassStructure my_trg_class;
  /**  Our Logger for this session.  */
  private CCLogManager my_logger;
  /**  Sourcelocation for target class, is needed very often.  */
  private BeetlzSourceLocation my_src;
  /**  User profile.  */
  private UserProfile my_profile;

  /**
   * Create a new class translator.
   * @param a_log_mng manager to do the logging
   * @param a_profile user profile
   */
  public ClassTranslator(final CCLogManager a_log_mng, final UserProfile a_profile) {
    my_logger = a_log_mng;
    my_profile = a_profile;
  }


  /**
   * Does the actual comparison.
   * @param a_src_class source class
   * @param a_trg_class target class
   * @return success value
   */
  public double doCheck(final ClassStructure a_src_class,
                        final ClassStructure a_trg_class) {
    my_src_class = a_src_class;
    my_trg_class = a_trg_class;
    my_trg_name = my_trg_class.getName();
    my_src = my_trg_class.getSourceLocation();

    double success = 0;
    if (!my_profile.pureBon()) {
      success += relateConstructor();
      success += relateEnum();
    }
    success += relateModifier();
    success += relateGenerics();
    success += relateInterfaces();
    success += relatePackage();
    success += relateClientRelations();
    if (!my_profile.noJml()) {
      success += relateClassSpecs();
    }
    success += relateFeatures();

    return success;

  }

  /**
   * Relate constructors.
   * @return success value
   */
  private double relateConstructor() {
    final double success = 1;
    if (!my_profile.pureBon()) { //do not check
      List < FeatureStructure > bon_constr;
      List < FeatureStructure > java_constr;
      if (my_src_class.getType() == ClassType.BON) {
        bon_constr = new Vector < FeatureStructure > (my_src_class.getConstructors());
        java_constr = new Vector < FeatureStructure > (my_trg_class.getConstructors());
      } else {
        java_constr = new Vector < FeatureStructure > (my_src_class.getConstructors());
        bon_constr = new Vector < FeatureStructure > (my_trg_class.getConstructors());
      }

      //for each BON constructor, try to find one that "fits" with constructor in Java
      final FeatureTranslator translator = new FeatureTranslator(my_logger, my_profile);
      for (final FeatureStructure bF : bon_constr) {
        boolean found = false;
        for (final FeatureStructure jF : java_constr) {
          if (translator.doQuickCheck(bF, jF) == 1) {
            found = true;
            if (my_src_class.getType() == ClassType.BON) {
              translator.doCheck(bF, jF);
            } else {
              translator.doCheck(jF, bF);
            }
          }
        }
        if (!found && my_src_class.getType() == ClassType.BON) {
          my_logger.logMissingConstructor(my_src, my_trg_name);
        } else if (!found && my_src_class.getType() == ClassType.JAVA) {
          my_logger.logRedundantConstructor(my_src, my_trg_name);
        }
      }
    }
    return success;
  }

  /**
   * Relate enums.
   * @return success value
   */
  private double relateEnum() {
    final double success = 1;
    if (my_src_class.isEnum() && !my_trg_class.isEnum()) {
      my_logger.logExpectedEnum(my_src, my_trg_name);
    } else if (!my_src_class.isEnum() && my_trg_class.isEnum()) {
      my_logger.logShouldNotEnum(my_src, my_trg_name);
    }

    return success;
  }

  /**
   * Relate modifier.
   * @return success value
   */
  private double relateModifier() {
    double success = 1;
    //-------ABSTRACT--------
    if (my_src_class.isAbstract()) {
      if (!my_trg_class.isAbstract()) {
        my_logger.logExpectedClassModifier(my_src, my_trg_name, ClassModifier.ABSTRACT);
        success = 0;
      }
    } else {
      if (my_trg_class.isAbstract()) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.ABSTRACT);
      }
    }
    //-------ROOT-------
    if (my_src_class.isRoot()) {
      if (!my_trg_class.isRoot()) {
        my_logger.logExpectedClassModifier(my_src, my_trg_name, ClassModifier.ROOT);
        success = 0;
      }
    } else {
      if (my_trg_class.isRoot()) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.ROOT);
        success = 0;
      }
    }
    //-------PERSISTENT-------
    if (my_src_class.isPersistent()) {
      if (!my_trg_class.isPersistent()) {
        my_logger.logExpectedClassModifier(my_src, my_trg_name, ClassModifier.PERSISTENT);
        success = 0;
      }
    } else {
      if (my_trg_class.isPersistent()) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.PERSISTENT);
        success = 0;
      }
    }
    //Now do the rest
    if (my_profile.javaIsSource()) {
      success = relateJavaToBonModifier();
    } else {
      success = relateBonToJavaModifier();
    }
    return success;
  }

  /**
   * Relate Java to BON modifier.
   * @return success value
   */
  private double relateJavaToBonModifier() {
    //STRICTPF is being ignored
    final SortedSet < ClassModifier > mods = my_src_class.getModifiers();
    double success = 1;
    //-------FINAL, STATIC and NONE--------
    if (mods.contains(ClassModifier.FINAL) ||
        mods.contains(ClassModifier.STATIC) || mods.size() == 0) {
      if (my_trg_class.isAbstract()) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.ABSTRACT);
        success = 0;
      }
    }
    //-----------INTERFACED ----------
    if (my_trg_class.isBonInterfaced()) {
      boolean all_public = true;
      for (final FeatureStructure f : my_src_class.getFeatures()) {
        if (!f.isPublic()) {
          all_public = false;
        }
      }
      if (!all_public) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.INTERFACED);
        success = 0;
      }
    }
    return success;
  }

  /**
   * Relate Bon to Java modifier.
   * @return success value
   */
  private double relateBonToJavaModifier() {
    //REUSED is being handled in the CheckManager
    double success = 1;
    final SortedSet < ClassModifier > bMods = my_src_class.getModifiers();
    //-------EFFECTIVE-------
    if (bMods.contains(ClassModifier.EFFECTIVE)) {
      if (my_trg_class.isAbstract()) {
        my_logger.logShouldNotClassModifier(my_src, my_trg_name, ClassModifier.ABSTRACT);
        success = 0;
      }
    }
    //-------INTERFACED-------
    if (bMods.contains(ClassModifier.INTERFACED)) {
      boolean all_public = true;
      for (final FeatureStructure f : my_trg_class.getFeatures()) {
        if (!f.isPublic()) {
          all_public = false;
        }
      }
      if (!all_public) {
        my_logger.logExpectedAllPublic(my_src, my_trg_name);
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
    double success = 1;

    if (!(my_trg_class.getGenerics().size() == my_src_class.getGenerics().size())) {
      my_logger.logIncorrectGenericsNumber(my_src, my_trg_name,
                                           my_src_class.getGenerics().size(), my_trg_class
                                           .getGenerics().size());
      success = 0;
    //correct number of generics
    } else {
      final PriorityQueue < SmartString > srcGen =
        new PriorityQueue < SmartString > (my_src_class.getGenerics());
      final PriorityQueue < SmartString > trgGen =
        new PriorityQueue < SmartString > (my_trg_class.getGenerics());

      final int size = my_src_class.getGenerics().size();
      for (int i = 0; i < size; i++) {
        final SmartString srcG = srcGen.poll();
        final SmartString trgG = trgGen.poll();
        if (srcG.compareToTyped(trgG) != 0) {
          my_logger.logIncorrectGenerics(my_src, my_trg_name, srcG, trgG);
        }
      }
    }
    return success;
  }

  /**
   * Relate interfaces.
   * @return success value
   */
  private double relateInterfaces() {
    double success = 1;
    final SortedSet < SmartString > src = my_src_class.getInterfaces();
    final SortedSet < SmartString > trg = my_trg_class.getInterfaces();

    //What is missing
    for (final SmartString s : src) {
      if (!Helper.containsTyped(trg, s) && Helper.typeKnown(s)) {
        System.err.println("type " + s + "  " + Helper.typeKnown(s));
        my_logger.logMissingInterface(my_src, my_trg_name, s);
        success = 0;
      }
    }

    //What is too much
    for (final SmartString s : trg) {
      if (!Helper.containsTyped(src, s) && Helper.typeKnown(s)) {
        my_logger.logRedundantInterface(my_src, my_trg_name, s);
        success = 0;
      }
    }
    return success;
  }

  /**
   * Relate client relations.
   * @return success value
   */
  private double relateClientRelations() {
    double success = 1;
    final List < SmartString > srcA =
      new Vector < SmartString > (my_src_class.getKnownSharedAssociations());
    final List < SmartString > trgA =
      new Vector < SmartString > (my_trg_class.getKnownSharedAssociations());
    
    //What is missing
    for (final SmartString s : srcA) {
      if (!Helper.containsTyped(trgA, s)) {
        my_logger.logMissingSharedAssociation(my_src, my_trg_name, s);
        success = 0;
      }
    }

    //What is too much
    for (final SmartString s : trgA) {
      if (!Helper.containsTyped(srcA, s)) {
        my_logger.logRedundantSharedAssociation(my_src, my_trg_name, s);
        success = 0;
      }
    }


    final List < SmartString > srcAggr =
      new Vector < SmartString > (my_src_class.getKnownAggregations());
    final List < SmartString > trgAggr =
      new Vector < SmartString > (my_trg_class.getKnownAggregations());

    //What is missing
    for (final SmartString s : srcAggr) {
      if (!Helper.containsTyped(trgAggr, s)) {
        my_logger.logMissingAggregation(my_src, my_trg_name, s);
        success = 0;
      }
    }

    //What is too much
    for (final SmartString s : trgAggr) {
      if (!Helper.containsTyped(srcAggr, s)) {
        my_logger.logRedundantAggregation(my_src, my_trg_name, s);
        success = 0;
      }
    }


    return success;
  }

  /**
   * Relate packages.
   * @return success value
   */
  private double relatePackage() {
    double success = 1;
    final int eight = 8;
    final SmartString srcP = my_src_class.getInnermostPackage();
    final SmartString trgP = my_trg_class.getInnermostPackage();
    if (!srcP.equalsTyped(trgP)) {
      String s = srcP.toString();
      String t = trgP.toString();
      if (s.endsWith(BConst.CLUSTER_SUFFIX)) {
        s = s.substring(0 , s.length() - eight).toLowerCase();
      }
      if (t.endsWith(BConst.CLUSTER_SUFFIX)) {
        t = t.substring(0 , t.length() - eight).toLowerCase();
      }
      if (!s.equals(t)) {
        my_logger.logIncorrectPackage(my_src, my_trg_name,
                                      my_src_class.getInnermostPackage(),
                                      my_trg_class.getInnermostPackage());
        success = 0;
      }
    }

    return success;
  }

  /**
   * Relate class specs.
   * @return success value
   */
  private double relateClassSpecs() {
    double success = 1;
    final JMLClassTranslator translator = new JMLClassTranslator(my_logger, my_profile);
    success = translator.doCheck(my_src_class, my_trg_class, my_src);
    return success;
  }

  /**
   * Relate features.
   * @return success value
   */
  private double relateFeatures() {
    double success = 1;
    final List < FeatureStructure > missingFeatures = new ArrayList < FeatureStructure > ();
    final List < ClassStructure > missingFeatureClasses = new ArrayList < ClassStructure > ();
    final List < FeatureStructure > trgFeatures =
      new ArrayList < FeatureStructure > (my_trg_class.getAccessibleFeatures());
    final FeatureTranslator translator = new FeatureTranslator(my_logger, my_profile);
    for (final FeatureStructure srcF : my_src_class.getAccessibleFeatures()) {
      //Try to find mapping in dictionary
      final String map = my_profile.getFeatureMapping(srcF.getSimpleName(),
                                                      my_src_class.getQualifiedName().
                                                      toString(),
                                                      my_trg_class.getQualifiedName().
                                                      toString());
      if (map != null) {
        final List < FeatureStructure > list =
          new Vector < FeatureStructure > (my_trg_class.hasExactFeature(new SmartString(map)));
        if (list.size() == 1) {
          success += translator.doCheck(srcF, list.get(0));
          trgFeatures.remove(list.get(0));
        } else {
          boolean found = false;
          for (final FeatureStructure trgF : list) {
            if (translator.doQuickCheck(srcF, trgF) == 0) {
              success += translator.doCheck(srcF, trgF);
              trgFeatures.remove(trgF);
              found = true;
            }
          }
          if (!found) {
            my_logger.logIncorrectMapping(my_src, srcF.getSimpleName());
          }
        }
      } else if (my_trg_class.hasExactFeature(srcF.getName()).size() == 1) { //NO MAPPING
        success +=
          translator.doCheck(srcF, my_trg_class.hasExactFeature(srcF.getName()).first());
        trgFeatures.remove(my_trg_class.hasExactFeature(srcF.getName()).first());
      //NO MAPPING, AMBIGUOUS
      } else if (my_trg_class.hasExactFeature(srcF.getName()).size() > 1) {
        final List < FeatureStructure > list =
          new Vector < FeatureStructure > (my_trg_class.hasExactFeature(srcF.getName()));

        boolean found = false;
        for (final FeatureStructure trgF : list) {
          if (translator.doQuickCheck(srcF, trgF) != 0) {
            success += translator.doCheck(srcF, trgF);
            trgFeatures.remove(trgF);
            found = true;
          }
        }
        if (!found) {
          if (Helper.testIsAccessor(my_src_class, srcF)) {
            continue;
          }
          if (my_src_class.getType() == ClassType.JAVA &&
              srcF.getSimpleName().equals(BConst.METHOD_MAIN)) {
            continue; //static main is not being compared
          }

          missingFeatures.add(srcF);
          missingFeatureClasses.add(my_trg_class);
        }

      } else { //NOTHING FOUND
        if (Helper.testIsAccessor(my_src_class, srcF)) {
          continue;
        }
        if (my_src_class.getType() == ClassType.JAVA &&
            srcF.getSimpleName().equals(BConst.METHOD_MAIN)) {
          continue; //static main is not being compared
        }

        missingFeatures.add(srcF);
        missingFeatureClasses.add(my_trg_class);
      }

    }
    if (missingFeatures.size() > 0) {
      my_logger.logMissingFeature(my_trg_name, missingFeatures, missingFeatureClasses);
    }
    if (Beetlz.getProfile().javaIsSource() && !trgFeatures.isEmpty()) {
      my_logger.logRedundantFeature(my_trg_name, trgFeatures);
    }
    return success;
  }



}

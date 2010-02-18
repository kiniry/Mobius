/**
 * Package with utility classes.
 */
package utils;

import java.util.List;

import logic.BeetlzExpression.Nullity;
import main.Beetlz;
import main.UserProfile;
import structure.ClassStructure;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.FeatureModifier;
import utils.smart.ParametrizedSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;
import utils.smart.WildcardSmartString;
import utils.smart.GenericParameter;
import utils.smart.WildcardSmartString.WildcardType;

/**
 * Formatter for formatting Java to BON strings
 * and vice versa.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class PrettyFormatter {
  /** Need this for formatting strings. */
  private static final int TWO = 2;
  /** Global profile of user settings. */
  private static UserProfile my_profile = Beetlz.getProfile();
  /** Formatting to Java. */
  private boolean my_to_java;


  /**
   * Create a new Formatter.
   * @param the_to_java whether formatting to java
   */
  public PrettyFormatter(final boolean the_to_java) {
    my_to_java = the_to_java;
  }

  public void setToJava(boolean myToJava) {
    my_to_java = myToJava;
  }



  /**
   * Get a formatted string of a type.
   * @param a_type type to format
   * @return formatted type
   */
  public final String getType(final SmartString a_type) {
    if (my_to_java) {
      return getJavaType(a_type);
    } else {
      return getBonType(a_type);
    }
  }

  /**
   * Get a formatted feature modifier.
   * @param a_mod modifier to format
   * @return formatted modifier
   */
  public final String getFeatMod(final FeatureModifier a_mod) {
    if (my_to_java) {
      return getJavaFeatMod(a_mod);
    } else {
      return getBonFeatMod(a_mod);
    }
  }

  /**
   * Get a class modifier.
   * @param a_mod modifier to format
   * @return formatted modifier
   */
  public final String getClassMod(final ClassModifier a_mod) {
    if (my_to_java) {
      return getJavaClassMod(a_mod);
    } else {
      return getBonClassMod(a_mod);
    }
  }

  /**
   * Formats a class name.
   * @param a_name class name to format
   * @return formatted class name
   */
  public final String getClassName(final SmartString a_name) {
    return getClassName(a_name, my_to_java);
  }
  
  private final String getClassName(final SmartString a_name, final boolean to_java) {
    if (to_java) {
      return formatJavaClassName(a_name.toString());
    } else {
      return formatBonClassName(a_name.toString());
    }
  }

  /**
   * Format a feature modifier to Java format.
   * @param a_mod feature modifier
   * @return Java formatted modifier
   */
  public static String getJavaFeatMod(final FeatureModifier a_mod) {
    if (a_mod == FeatureModifier.ABSTRACT) {
      return "abstract"; //$NON-NLS-1$
    }
    if (a_mod == FeatureModifier.REDEFINED) {
      return "@Override"; //$NON-NLS-1$
    } else {
      return a_mod.toString();
    }
  }

  /**
   * Format a feature modifier to BON format.
   * @param a_mod modifier to format
   * @return BON formatted modifier
   */
  public static String getBonFeatMod(final FeatureModifier a_mod) {
    if (a_mod == FeatureModifier.ABSTRACT) {
      return "deferred"; //$NON-NLS-1$
    } else {
      return a_mod.toString();
    }
  }

  /**
   * Format class modifier to Java format.
   * @param a_mod modifier to format
   * @return Java formatted modifier
   */
  public static String getJavaClassMod(final ClassModifier a_mod) {
    if (a_mod == ClassModifier.ABSTRACT) {
      return "abstract"; //$NON-NLS-1$
    }
    if (a_mod == ClassModifier.ROOT) {
      return "implementing Runnable"; //$NON-NLS-1$
    }
    if (a_mod == ClassModifier.PERSISTENT) {
      return "implementing Serializable"; //$NON-NLS-1$
    } else {
      return a_mod.toString();
    }
  }

  /**
   * Format a class modifier to BON format.
   * @param a_mod class modifier
   * @return Java formatted class modifier
   */
  public static String getBonClassMod(final ClassModifier a_mod) {
    if (a_mod == ClassModifier.ABSTRACT) {
      return "deferred"; //$NON-NLS-1$
    } else {
      return a_mod.toString();
    }
  }

  /**
   * Get string representation of nullity enumerated type.
   * @param the_nullity nullity to get string of
   * @return string representation
   */
  public static String getNullity(final Nullity the_nullity) {
    if (the_nullity == Nullity.NON_NULL) {
      return "non_null"; //$NON-NLS-1$
    } else {
      return "nullable"; //$NON-NLS-1$
    }
  }

  /**
   * Format a string to Java format.
   * @param a_string string to format
   * @return formatted string
   */
  public static String formatToJava(final String a_string) {
    if (a_string.length() == 0) {
      return ""; //$NON-NLS-1$
    }
    final String[] parts = a_string.split("_"); //$NON-NLS-1$
    String name = ""; //$NON-NLS-1$
    for (final String s : parts) {
      final String temp = s.trim().toLowerCase();
      final String first = "" + s.trim().charAt(0); //$NON-NLS-1$
      name += first + temp.substring(1);
    }
    return name;
  }

  /**
   * Format s string to BON format.
   * @param a_string string to format
   * @return formatted string
   */
  public static String formatToBon(final String a_string) {
    String name  = a_string;
    int index = name.lastIndexOf('.');
    if (index != -1 && index != name.length()) {
      name = name.substring(index + 1);
    }
    index = name.lastIndexOf('$');
    if (index != -1 && index != name.length()) {
      name = name.substring(index + 1);
    }

    String s = ""; //$NON-NLS-1$
    String buffer = ""; //$NON-NLS-1$
    final char[] ch = name.toCharArray();
    int i = 0;
    boolean lower = true;
    while (i < ch.length) {
      final char next = ch[i++];
      if (Character.isUpperCase(next) && lower) {
        s += buffer.toUpperCase() + "_"; //$NON-NLS-1$
        buffer = "" + next; //$NON-NLS-1$
        lower = false;
      } else if (Character.isUpperCase(next)) {
        buffer += next;
      } else {
        buffer += next;
        lower = true;
      }
    }
    s += buffer.toUpperCase();
    if (s.startsWith("_")) { //$NON-NLS-1$
      return s.substring(1);
    } else {
      return s;
    }

  }

  /**
   * Get a Java formatted type.
   * @param a_type type to format
   * @return formatted string
   */
  public static String getJavaType(final SmartString a_type) {
    if (a_type instanceof ParametrizedSmartString) {
      final ParametrizedSmartString paramStr = (ParametrizedSmartString) a_type;
      final List < SmartString > parts = (paramStr.getParams());
      String my_string = ""; //$NON-NLS-1$
      String map = my_profile.getClassMapping(paramStr.getName().toString());
      if (map != null) {
        my_string += map;
      } else {
        my_string += getJavaType(paramStr.getName());
      }
      String args = ""; //$NON-NLS-1$
      if (parts.size() > 0) {
        args += "<"; //$NON-NLS-1$
        for (int i = 0; i < parts.size(); i++) {
          map = my_profile.getClassMapping(parts.get(i).toString());
          if (map != null) {
            args += map + ", "; //$NON-NLS-1$
          }
          map = my_profile.getBasicDictionary().getBonToJavaMapping(my_string);
          if (map != null) {
            args += map + ", "; //$NON-NLS-1$
          } else {
            args += getJavaType(parts.get(i)) + ", "; //$NON-NLS-1$
          }
        }
        args = args.substring(0, args.length() - TWO);
        args += ">";  //$NON-NLS-1$
      }
      if (my_string.equals("Aray")) { //$NON-NLS-1$
        return args.substring(1, args.length() - 1) + "[]"; //$NON-NLS-1$
      } else {
        return my_string + args;
      }
      //ParametrizedSmartString
    } else if (a_type instanceof WildcardSmartString) {
      final WildcardSmartString w = (WildcardSmartString) a_type;
      if (w.getType() != WildcardType.NONE) {
        return "? " + w.getType().getName() + " " + w.getBound(); //$NON-NLS-1$ //$NON-NLS-2$
      }
      return "?"; //$NON-NLS-1$
      //WildcardSmartString
    } else if (a_type instanceof GenericParameter) {
      final GenericParameter g = (GenericParameter) a_type;
      if (g.getTypes().size() == 0) {
        return g.getDummyName();
      } else {
        return g.getDummyName() + " extends " + getJavaType(g.getTypes().get(0)); //$NON-NLS-1$
      }

    } else {
      String my_string = a_type.toString();
      String map = my_profile.getClassMapping(my_string);
      if (map != null) {
        final TypeSmartString ss = new TypeSmartString(map);
        return ss.getSimpleName();
      }
      map = my_profile.getBasicDictionary().getBonToJavaMapping(my_string);
      if (map != null) {
        return map;
      }
      int index = my_string.lastIndexOf('.');
      if (index != -1 && index != my_string.length()) {
        my_string = my_string.substring(index + 1);
      }
      index = my_string.lastIndexOf('$');
      if (index != -1 && index != my_string.length()) {
        my_string = my_string.substring(index + 1);
      }
      return formatToJava(my_string);
    } //else SmartString
  }

  /**
   * Get BON formatted type.
   * @param a_string string to format
   * @return formatted string
   */
  public static String getBonType(final SmartString a_string) {
    if (a_string instanceof ParametrizedSmartString) {
      final ParametrizedSmartString paramStr = (ParametrizedSmartString) a_string;
      final List < SmartString > parts = (paramStr.getParams());
      String my_string = ""; //$NON-NLS-1$
      String map = my_profile.getClassMapping(paramStr.getName().toString());
      if (map != null) {
        my_string += map;
      } else {
        my_string += getBonType(paramStr.getName());
      }
      if (parts.size() > 0) {
        my_string += "["; //$NON-NLS-1$
        for (int i = 0; i < parts.size(); i++) {
          map = my_profile.getClassMapping(parts.get(i).toString());
          if (map != null) {
            my_string += map + ", ";  //$NON-NLS-1$
          }
          map = my_profile.getBasicDictionary().getJavaToBonMapping(my_string);
          if (map != null) {
            my_string += map + ", "; //$NON-NLS-1$
          } else {
            my_string += getBonType(parts.get(i)) + ", "; //$NON-NLS-1$
          }
        }
        my_string = my_string.substring(0, my_string.length() - TWO);
        my_string += "]";  //$NON-NLS-1$
      }
      return my_string;
      //ParametrizedSmartString
    } else if (a_string instanceof WildcardSmartString) {
      final WildcardSmartString w = (WildcardSmartString) a_string;
      if (w.getType() == WildcardType.NONE) {
        return BConst.ANY;
      } else {
        return getBonType(((WildcardSmartString)a_string).getBound());
      }
      //WildcardSmartString
    } else if (a_string instanceof GenericParameter) {
      final GenericParameter g = (GenericParameter) a_string;
      if (g.getTypes().size() == 0) {
        return g.getDummyName();
      } else {
        return g.getDummyName() + " -> " + g.getTypes().get(0); //$NON-NLS-1$
      }
    } else {
      String my_string = a_string.toString();
      String map = my_profile.getClassMapping(my_string);
      if (map != null) {
        my_string = map;
      }
      map = my_profile.getBasicDictionary().getJavaToBonMapping(my_string);
      if (map != null) {
        return map;
      }
      return formatToBon(my_string);
    } //else SmartString
  }

  /**
   * Get Java formatted string.
   * @param a_name class name to format
   * @return formatted class name
   */
  public static String formatJavaClassName(final String a_name) {
    final String map = my_profile.getClassMapping(a_name);
    if (map != null) {
      final TypeSmartString ss = new TypeSmartString(map);
      return ss.getSimpleName();
    }
    final String[] parts = a_name.split("_"); //$NON-NLS-1$
    String name = ""; //$NON-NLS-1$
    for (final String s : parts) {
      final String temp = s.trim().toLowerCase();
      final String first = "" + s.trim().charAt(0); //$NON-NLS-1$
      name += first + temp.substring(1);
    }
    return name;
  }

  /**
   * Format a class name to BON format.
   * @param a_name class name to format
   * @return formatted string
   */
  public static String formatBonClassName(final String a_name) {
    final UserProfile profile = Beetlz.getProfile();
    final String my_string = a_name.toString();
    final String map = profile.getClassMapping(my_string);
    if (map != null) {
      final TypeSmartString ss = new TypeSmartString(map);
      return ss.getSimpleName();
    } else {
      return formatToBon(my_string);
    }
  }

}

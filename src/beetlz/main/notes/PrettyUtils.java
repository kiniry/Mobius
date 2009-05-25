/**
 * Package for pretty printing.
 */
package pretty;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import main.Beetlz;

import org.jmlspecs.openjml.JmlTree;

import utils.BasicTypesDictionary;
import utils.smart.ParametrizedSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;


import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

/**
 * Utility methods for pretty printing.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class PrettyUtils {
  /** Jml factory used. */
  private final JmlTree.Maker factory;
  /** Name table. */
  private final Name.Table nameTable;
  /** Map of primitive types. */
  private final Map < String, Integer > primitiveTypes;
  /** Map of basic types. */
  private final Map < String, String > basicTypes;
  /** Basic dictionary, link to the one in Beetlz. */
  private final BasicTypesDictionary dictionary;

  /**
   * Create a new PrettyUtils class and set up all necessary
   * types.
   * @param the_maker tree maker used
   * @param the_table name table used
   */
  public PrettyUtils(final JmlTree.Maker the_maker, final Name.Table the_table) {
    factory = the_maker;
    nameTable = the_table;
    dictionary = Beetlz.my_profile.basicDictionary;
    primitiveTypes = new HashMap < String, Integer > ();
    primitiveTypes.put("VALUE", TypeTags.INT); //$NON-NLS-1$
    primitiveTypes.put("INTEGER", TypeTags.INT); //$NON-NLS-1$
    primitiveTypes.put("REAL", TypeTags.DOUBLE); //$NON-NLS-1$
    primitiveTypes.put("BOOLEAN", TypeTags.BOOLEAN); //$NON-NLS-1$
    primitiveTypes.put("CHARACTER", TypeTags.CHAR); //$NON-NLS-1$

    basicTypes = new HashMap < String, String > ();
    basicTypes.put("VALUE", "Number"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("INTEGER", "Integer"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("REAL", "Double"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("BOOLEAN", "Boolean"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("CHARACTER", "Character"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("STRING", "String"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("ANY", "Object"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("SET", "Set"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("SEQUENCE", "List"); //$NON-NLS-1$ //$NON-NLS-2$
    basicTypes.put("TABLE", "Map"); //$NON-NLS-1$ //$NON-NLS-2$

  }

  
  public List < JCExpression > createList(final Vector< JCExpression > pieces) {
    if (pieces.size() == 0) {
      return List.nil();
    }

    List < JCExpression > args = List.of(pieces.firstElement());
    for (int i = 1; i < pieces.size(); i++) {
      args = args.append(pieces.get(i));
    }
    return args;
  }

  public List < JCTree > createJCTreeList(final Vector< JCTree > pieces) {
    if (pieces.size() == 0) {
      return List.nil();
    }

    List < JCTree > args = List.of(pieces.firstElement());
    for (int i = 1; i < pieces.size(); i++) {
      args = args.append(pieces.get(i));
    }
    return args;
  }

  public List < JCTypeParameter > createTypeParamList(final Vector< JCTypeParameter > pieces) {
    if (pieces.size() == 0) {
      return List.nil();
    }

    List < JCTypeParameter > args = List.of(pieces.firstElement());
    for (int i = 1; i < pieces.size(); i++) {
      args = args.append(pieces.get(i));
    }
    return args;
  }

  public List < JCVariableDecl > createVariableDeclList(final Vector< JCVariableDecl > pieces) {
    if (pieces.size() == 0) {
      return List.nil();
    }

    List < JCVariableDecl > args = List.of(pieces.firstElement());
    for (int i = 1; i < pieces.size(); i++) {
      args = args.append(pieces.get(i));
    }
    return args;
  }



  public JCExpression getObjectType(final SmartString s) {
    if (s instanceof ParametrizedSmartString) {
      final ParametrizedSmartString p_str = (ParametrizedSmartString) s;
      final JCExpression name = getObjectType(p_str.getName());
      final Vector < JCExpression > args = new Vector < JCExpression > ();
      for (final SmartString param : p_str.getParams()) {
        final JCExpression expr = getObjectType(param);
        args.add(expr);
      }
      final JCTypeApply i = factory.TypeApply(name, createList(args));
      return i;
    } else {
      final JCExpression i =
        factory.Ident(nameTable.fromString(translateClassName(s.toString())));
      return i;
    }
  }

  public JCExpression getGeneralType(final SmartString s) {
    if (s instanceof ParametrizedSmartString) {
      final ParametrizedSmartString p_str = (ParametrizedSmartString) s;
      final JCExpression name = getObjectType(p_str.getName());
      final Vector < JCExpression > args = new Vector < JCExpression >();
      for (final SmartString param: p_str.getParams()) {
        final JCExpression expr = getObjectType(param);
        args.add(expr);
      }
      final JCTypeApply i = factory.TypeApply(name, createList(args));
      return i;
    }

    if (primitiveTypes.containsKey(s.toString())){
      final JCExpression i = factory.TypeIdent(primitiveTypes.get(s.toString()));
      return i;
    }

    final JCExpression i = factory.Ident(nameTable.fromString(translateClassName(s.toString())));
    return i;

  }

  public Name getObjectName(final SmartString s) {
    if (s instanceof TypeSmartString) {
      return nameTable.fromString(translateClassName(((TypeSmartString)s).getSimpleName()));
    }
    return nameTable.fromString(translateClassName(s.toString()));
  }



  private String translateClassName(final String bonName) {
    if (basicTypes.containsKey(bonName)) {
      return basicTypes.get(bonName);
    }
    String map = dictionary.getBonToJavaMapping(bonName);
    if (map != null) {
      return map;
    }
    map = Beetlz.my_profile.getClassMapping(bonName);
    if (map != null) {
      return map;
    }
    return this.formatJavaName(bonName);
  }

  private String formatJavaName(final String a_name) {
    final String[] parts = a_name.split("_"); //$NON-NLS-1$
    String name = ""; //$NON-NLS-1$
    for (final String s: parts){
      final String temp = s.trim().toLowerCase();
      final String first = "" + s.trim().charAt(0); //$NON-NLS-1$
      name += first + temp.substring(1);
    }
    return name;
  }





}

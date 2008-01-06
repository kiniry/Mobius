package jml2bml.engine;



import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlToken;

import com.sun.source.tree.Tree;

public class Utils {
  public static int mapJCOperatorToBmlLib(JmlToken token) {
    return 0;
  }

  public static int mapJCOperatorToBmlLib(Tree.Kind kind) {
    return 0;
  }

  public static String mapJCTypeKindToBmlLib(TypeKind primitiveTypeKind) {
    if (TypeKind.BOOLEAN.compareTo(primitiveTypeKind) == 0) {
      return "boolean";
    }
    if (TypeKind.INT.compareTo(primitiveTypeKind) == 0) {
      return "int";
    }
    return null;
  }
}

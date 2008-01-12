package jml2bml.engine;



import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlToken;

import annot.io.Code;

import com.sun.tools.javac.tree.JCTree;

public class Utils {
  public static int mapJCOperatorToBmlLib(JmlToken token) {
    if (JmlToken.BSFORALL.equals(token))
      return Code.FORALL_WITH_NAME;
    if (JmlToken.BSEXISTS.equals(token))
      return Code.EXISTS_WITH_NAME;
    if (JmlToken.IMPLIES.equals(token))
      return Code.IMPLIES;
    //FIXME
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

  public static int mapJCTagToBmlLib(int tag) {
    if (tag == JCTree.AND)
    {
      return Code.AND;
    }
    if (tag == JCTree.OR){
      return Code.OR;
    }
    return -3;
  }

}

package jml2bml.bytecode;

import static com.sun.tools.javac.code.TypeTags.ARRAY;
import static com.sun.tools.javac.code.TypeTags.BOOLEAN;
import static com.sun.tools.javac.code.TypeTags.BYTE;
import static com.sun.tools.javac.code.TypeTags.CHAR;
import static com.sun.tools.javac.code.TypeTags.CLASS;
import static com.sun.tools.javac.code.TypeTags.DOUBLE;
import static com.sun.tools.javac.code.TypeTags.FLOAT;
import static com.sun.tools.javac.code.TypeTags.INT;
import static com.sun.tools.javac.code.TypeTags.LONG;
import static com.sun.tools.javac.code.TypeTags.METHOD;
import static com.sun.tools.javac.code.TypeTags.SHORT;
import static com.sun.tools.javac.code.TypeTags.TYPEVAR;
import static com.sun.tools.javac.code.TypeTags.VOID;
import static com.sun.tools.javac.code.TypeTags.WILDCARD;
import jml2bml.exceptions.Jml2BmlException;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.WildcardType;
import com.sun.tools.javac.util.List;

public class TypeSignature {

  private StringBuffer result = new StringBuffer();

  
  public static String getSignature(Type type) {
    TypeSignature sign = new TypeSignature();
    sign.assembleSig(type);
    return sign.result.toString();
  }
  
  public void assembleSig(Type type) {
    switch (type.tag) {
      case BYTE:
        result.append('B');
        break;
      case SHORT:
        result.append('S');
        break;
      case CHAR:
        result.append('C');
        break;
      case INT:
        result.append('I');
        break;
      case LONG:
        result.append('J');
        break;
      case FLOAT:
        result.append('F');
        break;
      case DOUBLE:
        result.append('D');
        break;
      case BOOLEAN:
        result.append('Z');
        break;
      case VOID:
        result.append('V');
        break;
      case CLASS:
        result.append('L');
        result.append(type.toString());
//        assembleClassSig(type);
        result.append(';');
        break;
      case ARRAY:
        ArrayType at = (ArrayType) type;
        result.append('[');
        assembleSig(at.elemtype);
        break;
      case METHOD:
        MethodType mt = (MethodType) type;
        result.append('(');
        assembleSig(mt.argtypes);
        result.append(')');
        assembleSig(mt.restype);
        if (hasTypeVar(mt.thrown)) {
          for (List < Type > l = mt.thrown; l.nonEmpty(); l = l.tail) {
            result.append('^');
            assembleSig(l.head);
          }
        }
        break;
      case WILDCARD: {
        WildcardType ta = (WildcardType) type;
        switch (ta.kind) {
          case SUPER:
            result.append('-');
            assembleSig(ta.type);
            break;
          case EXTENDS:
            result.append('+');
            assembleSig(ta.type);
            break;
          case UNBOUND:
            result.append('*');
            break;
          default:
            throw new AssertionError(ta.kind);
        }
        break;
      }
      case TYPEVAR:
        result.append('T');
        result.append(type.tsym.name.toString());
        result.append(';');
        break;
      default:
        throw new Jml2BmlException("Unknown typeSig " + type.tag+ ":"+type);
    }
  }

//  private void assembleClassSig(Type type) {
//    ClassType ct = (ClassType) type;
//    ClassSymbol c = (ClassSymbol) ct.tsym;
//    enterInner(c);
//    Type outer = ct.getEnclosingType();
//    if (outer.allparams().nonEmpty()) {
//      boolean rawOuter = c.owner.kind == MTH || // either a local class
//                         c.name == names.empty; // or anonymous
//      assembleClassSig(rawOuter ? types.erasure(outer) : outer);
//      result.append('.');
//      assert c.flatname.startsWith(c.owner.enclClass().flatname);
//      result.append(rawOuter ? c.flatname.subName(c.owner.enclClass().flatname
//          .getByteLength() + 1, c.flatname.getByteLength()) : c.name);
//    } else {
//      result.append(externalize(c.flatname));
//    }
//    if (ct.getTypeArguments().nonEmpty()) {
//      result.append('<');
//      assembleSig(ct.getTypeArguments());
//      result.append('>');
//    }
//  }

  private void assembleSig(List < Type > types) {
    for (List < Type > ts = types; ts.nonEmpty(); ts = ts.tail)
      assembleSig(ts.head);
  }

  private boolean hasTypeVar(List < Type > l) {
    while (l.nonEmpty()) {
      if (l.head.tag == TypeTags.TYPEVAR)
        return true;
      l = l.tail;
    }
    return false;
  }
  
//  private void assembleParamsSig(List<Type> typarams) {
//    result.append('<');
//    for (List<Type> ts = typarams; ts.nonEmpty(); ts = ts.tail) {
//        TypeVar tvar = (TypeVar)ts.head;
//        result.append(tvar.tsym.name);
//        List<Type> bounds = types.getBounds(tvar);
//        if ((bounds.head.tsym.flags() & INTERFACE) != 0) {
//            result.append(':');
//        }
//        for (List<Type> l = bounds; l.nonEmpty(); l = l.tail) {
//            result.append(':');
//            assembleSig(l.head);
//        }
//    }
//    result.append('>');
//}
}

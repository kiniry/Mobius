package jml2bml.utils;

import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.source.tree.ExpressionTree;

public final class JCUtils {
  public static boolean isOld(ExpressionTree node){
    if ("\\old".equals(node.toString())){
    return true;
    }
    return false;
  }
  public static boolean isPre(ExpressionTree node){
    if ("\\pre".equals(node.toString())){
      return true;
      }
      return false;
    }
  public static boolean isResult(JmlSingleton node) {
    if ("BSRESULT".equals(node.token.name())){
      return true;
    }
    return false;
  }
}

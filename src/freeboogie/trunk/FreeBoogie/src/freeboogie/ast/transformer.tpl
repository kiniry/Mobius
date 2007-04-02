A transformer takes a tree and generates another. The methods
here implement path-compression. 

\file{Transformer.java}
/**
  Public domain.
  This file was generated from transformer.tpl. Do not edit.
 */
package freeboogie.ast;

public class Transformer extends Evaluator<Ast> {
\normal_classes{
  @Override
  public \ClassName eval(
    \ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} 
      \memberName
    }
  ) {
    boolean sameChildren = true;
    \members{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      new\MemberName = 
        \if_primitive{\memberName}{(\MemberType)\memberName.eval(this)};
      \if_primitive{}{sameChildren &= new\MemberName == \memberName;}
    }
    if (sameChildren) return \className;
    return new \ClassName(
      \members[,]{new\MemberName}
    );
  }   
}
}

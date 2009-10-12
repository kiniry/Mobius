This template generates java classes for the abstract classes.

\abstract_classes{\file{\ClassName.java}
/**
  This class is generated automatically from abstract_classes.tpl.
  Do not edit.
 */
package \Userdefine{pkg};

import ie.ucd.bon.source.SourceLocation;

public abstract class \ClassName extends \Basename {

  public \ClassName(SourceLocation location) {
    super(location);
  }

  // a more specific return type
  @Override
  public abstract \ClassName clone();
}
}

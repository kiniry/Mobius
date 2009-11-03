This template generates java classes for the abstract classes.

\abstract_classes{\file{\ClassName.java}
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from abstract_classes.tpl.
 * Do not edit.
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

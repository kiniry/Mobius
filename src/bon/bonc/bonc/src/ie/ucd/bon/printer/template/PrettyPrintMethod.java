/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer.template;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.util.StringUtil;

import java.util.List;

import freemarker.template.TemplateMethodModelEx;
import freemarker.template.TemplateModelException;

public class PrettyPrintMethod implements TemplateMethodModelEx {


  @SuppressWarnings("unchecked")
  public Object exec(List arguments) throws TemplateModelException {
    if (arguments.size() != 1) {
      throw new TemplateModelException("Wrong arguments");
    }
    Object o = arguments.get(0);
    if (o instanceof AstNode) {
      return StringUtil.prettyPrint((AstNode)o);
    } else {
      throw new TemplateModelException("Wrong arguments, not a AstNode - " + o.getClass());
    }
  }

}

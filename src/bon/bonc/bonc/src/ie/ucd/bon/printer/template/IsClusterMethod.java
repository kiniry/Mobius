package ie.ucd.bon.printer.template;

import ie.ucd.bon.typechecker.BONST.BONSTInformal;

import java.util.List;

import freemarker.template.TemplateMethodModel;
import freemarker.template.TemplateModelException;

public class IsClusterMethod implements TemplateMethodModel {

  private final BONSTInformal st;
  
  public IsClusterMethod(BONSTInformal st) {
    super();
    this.st = st;
  }

  @SuppressWarnings("unchecked")
  @Override
  public Object exec(List arguments) throws TemplateModelException {
    if (arguments.size() != 1) {
      throw new TemplateModelException("Wrong arguments");
    }
    String s = arguments.get(0).toString();
    return st.clusters.containsKey(s);    
  }

}

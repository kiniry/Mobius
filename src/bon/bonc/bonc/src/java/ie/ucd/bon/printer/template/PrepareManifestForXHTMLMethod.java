/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer.template;

import ie.ucd.clops.util.StringUtil;

import java.util.List;

import freemarker.template.TemplateMethodModel;
import freemarker.template.TemplateModelException;

public class PrepareManifestForXHTMLMethod implements TemplateMethodModel {

  private static final String LINE_SEP = System.getProperty("line.separator");

  @SuppressWarnings("unchecked")
  public Object exec(List arguments) throws TemplateModelException {
    if (arguments.size() != 1) {
      throw new TemplateModelException("Wrong arguments");
    }
    String s = arguments.get(0).toString();

    String[] parts = s.split(LINE_SEP);
    String[] processedParts = new String[parts.length];

    for (int i=0; i < parts.length; i++) {
      processedParts[i] = process(parts[i], i == 0, i == parts.length-1);
    }

    return StringUtil.appendWithSeparator(processedParts, " ", false);
  }

  private static String process(String s, boolean isFirst, boolean isLast) {
    String trimmed = s.trim();

    if (isFirst && isLast) {
      return trimmed;
    }

    if (!isFirst && trimmed.charAt(0) == '\\') {
      trimmed = trimmed.substring(1);
    }
    if (!isLast && trimmed.charAt(trimmed.length()-1) == '\\') {
      trimmed = trimmed.substring(0,trimmed.length()-1);
    }
    return trimmed.trim();
  }

}

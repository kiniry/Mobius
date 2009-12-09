/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.printer.LatexPrintVisitor;
import ie.ucd.bon.printer.PrettyPrintVisitor;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Arrays;
import java.util.Collection;


public final class StringUtil {

  /** Private constructor, cannot be instantiated. */
  private StringUtil() { }

  public static String stripForHTML(final String mtb, boolean withSpeechMarks) {
    String stripped = strip(mtb);
    stripped = stripped.replace("&", "&amp;");
    stripped = stripped.replace("<", "&lt;");
    stripped = stripped.replace(">", "&gt;");

    StringBuilder sb = new StringBuilder();
    if (withSpeechMarks) {
      sb.append("&#8220;");
    }
    sb.append(stripped.substring(1, stripped.length()-1));
    if (withSpeechMarks) {
      sb.append("&#8221;");
    }
    return sb.toString();
  }

  public static String strip(final String mtb) {
    return stripManifestTextBlockToSingleLine(mtb);
  }

  public static String stripManifestTextBlockToSingleLine(final String mtb) {
    String[] lines = mtb.split("\\r?\\n");
    if (lines.length == 1) {
      return lines[0];
    }

    StringBuilder sb = new StringBuilder();
    sb.append(stripFirstLine(lines[0]));

    for (int i = 1; i < lines.length-1; i++) {
      sb.append(stripMiddleLine(lines[i]));
    }

    sb.append(stripLastLine(lines[lines.length-1]));
    return sb.toString();
  }

  private static String stripFirstLine(final String firstLine) {
    String trimmed = firstLine.trim();
    return trimmed.substring(0, trimmed.length()-1); //Lose trailing '/'
  }

  private static String stripLastLine(final String lastLine) {
    String trimmed = lastLine.trim();
    return trimmed.substring(1, trimmed.length()); //Lose leading '/'
  }

  private static String stripMiddleLine(final String middleLine) {
    String trimmed = middleLine.trim();
    return trimmed.substring(1, trimmed.length()-1); //Lose leading and trailing '/'
  }

  public static String getComponentNameFromStaticRef(String staticRef) {
    if (!staticRef.contains(".")) {
      return staticRef;
    } else {
      return staticRef.substring(staticRef.lastIndexOf("."));
    }
  }

  public static String timeString(final long timeInNano) {
    return timeInNano + "ns (" + (timeInNano / 1000000d) + "ms or " + (timeInNano / 1000000000d) + "s)";
  }

  public static String exceptionStackTraceAsString(Exception e) {
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    PrintStream ps = new PrintStream(baos);
    e.printStackTrace(ps);
    return baos.toString();
  }

  public static String appendWithSeparator(Collection<?> items, String sep) {
    return appendWithSeparator(items, sep, false);
  }

  public static String appendWithSeparator(Collection<?> items, String sep, boolean separatorAtEnd) {
    StringBuilder sb = new StringBuilder();
    for (Object o : items) {
      sb.append(o.toString());
      sb.append(sep);
    }
    if (sb.length() > 0 && !separatorAtEnd) {
      sb.delete(sb.length()-sep.length(), sb.length());
    }
    return sb.toString();
  }

  public static <T> String appendWithSeparator(T[] items, String sep, boolean separatorAtEnd) {
    return appendWithSeparator(Arrays.asList(items), sep, separatorAtEnd);
  }
  
  public static <T> String appendWithSeparator(T[] items, String sep) {
    return appendWithSeparator(Arrays.asList(items), sep);
  }
  
  private static final PrettyPrintVisitor ppv = new PrettyPrintVisitor();
  public static String prettyPrint(AstNode node) {
    if (node == null) {
      return "";
    }
    ppv.resetVisitorOutput();
    node.accept(ppv);
    return ppv.getVisitorOutputAsString();
  }
  
  public static String prettyPrintShortenedClass(Clazz clazz) {
    StringBuilder sb = new StringBuilder();
    sb.append(clazz.name.name);
    if (!clazz.generics.isEmpty()) {
      ppv.resetVisitorOutput();
      ppv.visitAllPrintingSeparator(clazz.generics, ", ", false);
      sb.append('[');
      sb.append(ppv.getVisitorOutputAsString());
      sb.append(']');
    }
    return sb.toString();
  }
  
  private static final LatexPrintVisitor lpv = new LatexPrintVisitor();
  public static String latexPrint(AstNode node) {
    if (node == null) {
      return "";
    }
    lpv.resetVisitorOutput();
    node.accept(lpv);
    return lpv.getVisitorOutputAsString();
  }

}

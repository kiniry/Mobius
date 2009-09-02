/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.clinterface.BONcOptionsInterface.Print;
import ie.ucd.bon.graph.Grapher;
import ie.ucd.bon.linguistical.MiscLing;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.ClassDictionaryGenerator;
import ie.ucd.bon.printer.PrettyPrintVisitor;
import ie.ucd.bon.printer.PrintAgent;
import ie.ucd.bon.printer.UnableToGenerateClassDictionaryException;
import ie.ucd.bon.printer.XHTMLPrintVisitor;
import ie.ucd.bon.util.StringUtil;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;

/**
 * 
 * @author Fintan
 *
 */
public final class Printer {

  /** Prevent instantiation of Printer. */
  private Printer() { }

  public static String getPrintingOptionName(final Print p) {
    switch(p) {
    case TXT:
      return "plain-text";
    case HTML:
      return "web-page format";
    case DOT:
      return ".dot graph format";
    case DIC:
      return "automatically generated class dictionary";
    case ICG:
      return "informal cluster graph";
    case IIG:
      return "informal class inheritance graph";
    case CL:
      return "linguistical analysis data";
    case PICG:
      return "informal cluster graph for prefuse";
    case PIIG:
      return "informal cluster graph for prefuse";
    default:
      return "unknown"; //Shouldn't happen
    }
  }

  public static boolean isFileIndependentPrintingOption(final Print p) {
    switch(p) {
    case DIC:
    case ICG:
    case IIG:
    case CL:
    case PICG:
    case PIIG:
      return true;
    default:
      return false;
    }
  }

  public static String printGeneratedClassDictionaryToString(final ParsingTracker tracker) {
    try {
      return ClassDictionaryGenerator.generateDictionary(tracker);
    } catch (UnableToGenerateClassDictionaryException e) {
      System.out.println("Unable to generate class dictionary: " + e.getMessage());
      return "";
    }
  }

  private static Map<String,Object> getAdditionalDataMap(final ParsingTracker parsingTracker) {
    Map<String,Object> additionalDataMap = new HashMap<String,Object>();
    additionalDataMap.put("version", Main.getVersion());
    ClusterChart sysDef = parsingTracker.getSymbolTable().informal.systemChart;
    additionalDataMap.put("systemName", sysDef == null ? "NO SYSTEM DEFINED" : sysDef.getName());
    additionalDataMap.put("time", new Date());
    return additionalDataMap;
  }


  private static PrintAgent getNewPrintAgent(final Print printingType, final ParsingTracker tracker) {
    switch(printingType) {
    case TXT:
      return new PrettyPrintVisitor();
    case HTML:
      return new XHTMLPrintVisitor(tracker);
    default:
      return null;
    }
  }

  public static void printToStream(final Collection<File> files, final ParsingTracker parsingTracker, final PrintStream outputStream, final Print printingType, final boolean timing) {
    Main.logDebug("Printing to stream.");
    long startTime = System.nanoTime();

    if (isFileIndependentPrintingOption(printingType)) {
      outputStream.print(printFileIndependentPrintingOptionToString(printingType, parsingTracker));
    } else {

      PrintAgent pa = getNewPrintAgent(printingType, parsingTracker);
      if (pa == null) {
        System.out.println("Something went wrong when printing.");
        return;
      }

      for (File file : files) {
        Main.logDebug("Printing for file: " + file);

        ParseResult parse = parsingTracker.getParseResult(file);
        if (parse.continueFromParse(Main.PP_NUM_SEVERE_ERRORS)) {
          BonSourceFile sf = parse.getParse();
          pa.visitBonSourceFile(sf, sf.bonSpecification, sf.indexing, sf.getLocation());
        } else {
          System.out.println("Not printing " + file + " due to parse errors.");
        }
      }

      Map<String,Object> additionalInfo = getAdditionalDataMap(parsingTracker);
      try {
        outputStream.print(pa.getAllOutputAsString(parsingTracker, additionalInfo));
      } catch (IOException ioe) {
        System.out.println("An error occurred while printing.");
      }
    }

    if (timing) {
      long endTime = System.nanoTime();
      System.out.println("Printing as " + Printer.getPrintingOptionName(printingType) + " took: " + StringUtil.timeString(endTime - startTime));
    }

  }

  private static String printFileIndependentPrintingOptionToString(final Print printingOption, final ParsingTracker parsingTracker) {
    switch (printingOption) {
    case DIC:
      return printGeneratedClassDictionaryToString(parsingTracker);
    case ICG:
      return Grapher.graphInformalClusterContainment(parsingTracker);
    case IIG:
      return Grapher.graphInformalClassInheritance(parsingTracker);
    case CL:
      return MiscLing.printClassChartSentences(parsingTracker);
    case PICG:
      //return Grapher.graphPrefuseInformalClusterContainment(parsingTracker);
    case PIIG:
      //return Grapher.graphPrefuseInformalInheritance(parsingTracker);
    default:
      return "";
    }
  }

}

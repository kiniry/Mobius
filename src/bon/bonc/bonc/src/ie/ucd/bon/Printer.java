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
import ie.ucd.bon.printer.LatexPrintVisitor;
import ie.ucd.bon.printer.NewHtmlPrinter;
import ie.ucd.bon.printer.PrettyPrintVisitor;
import ie.ucd.bon.printer.PrintAgent;
import ie.ucd.bon.printer.UnableToGenerateClassDictionaryException;
import ie.ucd.bon.printer.XHTMLPrintVisitor;
import ie.ucd.bon.util.StringUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
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
      case NEWHTML:
        return "new web-page format";
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
      case TEX:
        return "latex";
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

  /**
   * Does this print option produce a single file, or multiple files?
   * @param p the print option
   * @return a boolean indicating if this print option produces a single file
   */
  public static boolean isSingleFilePrintingOption(final Print p) {
    switch(p) {
      case NEWHTML:
        return false;
      default:
        return true;
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
      case TEX:
        return new LatexPrintVisitor();
      case HTML:
        return new XHTMLPrintVisitor(tracker);
      default:
        return null;
    }
  }

  public static void printToStream(final ParsingTracker parsingTracker, final PrintStream outputStream, final Print printingType, final boolean timing) {
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

      for (ParseResult parse : parsingTracker.getParses()) {
        File file = parse.getFile();
        Main.logDebug("Printing for file: " + file);

        if (parse.continueFromParse()) {
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
  
  private static void printSingleFile(final Print printType, final File outputFile, final ParsingTracker tracker, final boolean timing) {
    PrintStream outputStream;
    if (outputFile != null) {
      try {
        FileOutputStream outputFileStream = new FileOutputStream(outputFile);
        outputStream = new PrintStream(outputFileStream);

        Main.logDebug("printing: " + printType + ", to: " + outputFile.getPath());
      } catch (FileNotFoundException fnfe) {
        System.out.println("Error writing to file " + outputFile.getPath());
        return;
      }
    } else {
      outputStream = System.out;
      Main.logDebug("printing: " + printType + ", to: stdout");
    }

    Printer.printToStream(tracker, outputStream, printType, timing);

    if (outputFile != null) {
      outputStream.close();
      System.out.println("Succesfully created: " + outputFile.getPath());
    }
  }
  
  private static void printMultipleFiles(final Print printType, final File outputDirectory, final ParsingTracker tracker, final boolean timing) {
    //Check outputFile is a dir
    if (outputDirectory == null) {
      System.out.println("Must specify a directory for output for printing option for print type " + printType.name());
      return;
    }
    if (!outputDirectory.exists()) {
      System.out.println("Unable to print to " + outputDirectory.getPath() + ", as directory does not exist.");
      return;
    }
    if (!outputDirectory.isDirectory()) {
      System.out.println("Unable to print to " + outputDirectory.getPath() + ", as  it is not a directory.");
      return;
    }
    
    switch(printType) {
      case NEWHTML:
        NewHtmlPrinter.print(outputDirectory, tracker);
        break;
    }
  }
  
  public static void print(final Print printType, final File outputFile, final ParsingTracker tracker, final boolean timing) {
    if (isSingleFilePrintingOption(printType)) { 
      printSingleFile(printType, outputFile, tracker, timing);
    } else {
      printMultipleFiles(printType, outputFile, tracker, timing);
    }
  }

}

/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.clinterface.BONcOptionsInterface.Print;
import ie.ucd.bon.graph.Grapher;
import ie.ucd.bon.linguistical.MiscLing;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.ClassDictionaryGenerator;
import ie.ucd.bon.printer.HTMLLinkGenerator;
import ie.ucd.bon.printer.PrintingTracker;
import ie.ucd.bon.printer.UnableToGenerateClassDictionaryException;
import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.util.Calendar;
import java.util.Collection;
import java.util.GregorianCalendar;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.DOTTreeGenerator;
import org.antlr.stringtemplate.StringTemplateGroup;

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

  public static String getPrintingOptionStartString(final Print p) {
    try {
      switch(p) {
      case TXT:
        return FileUtil.readToString("templates/PlainTextStart.txt");
      case HTML:
        return FileUtil.readToString("templates/XHTMLStart.txt"); 
      default:
        return ""; //Shouldn't happen
      }
    } catch (IOException ioe) {
      Main.logDebug("IOException thrown whilst reading printing option start string");
      return "";
    }
  }

  public static String getPrintingOptionEndString(final Print p) {
    try {
      switch(p) {
      case TXT:
        return FileUtil.readToString("templates/PlainTextEnd.txt");
      case HTML:
        return FileUtil.readToString("templates/XHTMLEnd.txt"); 
      default:
        return ""; //Shouldn't happen
      }
    } catch (IOException ioe) {
      Main.logDebug("IOException thrown whilst reading printing option start string");
      return "";
    }
  }

  public static Reader getPrintingOptionTemplateFileReader(final Print p) {
    switch(p) {
    case TXT:
      return FileUtil.getResourceReader("templates/BONPlainText.stg");
    case HTML:
      return FileUtil.getResourceReader("templates/BONXHTML.stg"); 
    default:
      return null; //Shouldn't happen
    }
  }

  public static String getExtraPartsForPrintingOption(final Print p, final PrintingTracker printingTracker, final ParsingTracker parsingTracker) {
    switch(p) {
    case HTML:
      return HTMLLinkGenerator.generateLinks(printingTracker, parsingTracker);
    default:
      return "";
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

  private static String printUsingTemplateToString(final ParseResult parseResult, final Reader stFile, final Print printingOption, final PrintingTracker printingTracker) throws RecognitionException {
    try {
      StringTemplateGroup templates = new StringTemplateGroup(stFile);
      stFile.close();
      //TODO fix!
      return "";
//      CommonTree t = (CommonTree)parseResult.getParse().getTree(); //Get input tree
//      CommonTreeNodeStream nodes = new CommonTreeNodeStream(t);  //Get stream of nodes from tree
//      nodes.setTokenStream(parseResult.getTokens());
//
//      walker.initialise(nodes, templates, printingTracker, printingOption); //Reset walker, provide inputs
//
//      BONSTTreeWalker.prog_return r2 = walker.prog();  //Walk
//      StringTemplate output = (StringTemplate)r2.getTemplate();  //Get output
//      return output.toString();

    } catch (IOException ioe) {
      System.out.println("An error occurred whilst reading templateFile " + stFile);
      return null;
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

  public static String printDotToString(final ParseResult parseResult) {
    DOTTreeGenerator gen = new DOTTreeGenerator();
    //TODO fix!
    return "";
//    StringTemplate st = gen.toDOT((Tree)parseResult.getParse().getTree());
//    return st.toString();
  }

  private static String printStartToString(final Print printOption, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    return formatString(getPrintingOptionStartString(printOption), printTime, extraParts, parsingTracker);
  }

  private static String printEndToString(final Print printOption, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    return formatString(getPrintingOptionEndString(printOption), printTime, extraParts, parsingTracker);
  }

  private static String formatString(final String toFormat, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    ClusterChart sysDef = null; 
    sysDef = parsingTracker.getSymbolTable().informal.systemChart;
    String systemName = sysDef == null ? "NO SYSTEM DEFINED" : sysDef.getName(); 
    return String.format(toFormat, 
        printTime, 
        Main.getVersion(), 
        systemName,
        extraParts
    );
  }


  public static void printToStream(final Collection<File> files, final ParsingTracker parsingTracker, final PrintStream outputStream, final Print printingType, final boolean printToFile, final boolean timing) {
    Main.logDebug("Printing to stream.");
    Calendar printTime = new GregorianCalendar();
    PrintingTracker printTracker = new PrintingTracker();
    StringBuilder main = new StringBuilder();


    if (isFileIndependentPrintingOption(printingType)) {
      main.append(printFileIndependentPrintingOptionToString(printingType, parsingTracker));
    } else {

      for (File file : files) {
        Main.logDebug("Printing for file: " + file.getAbsolutePath());
        String fileName;
        if (file == null) {
          fileName = "stdin";
        } else {
          fileName = file.getPath();
        }

        ParseResult parse = parsingTracker.getParseResult(fileName);
        if (parse.continueFromParse(Main.PP_NUM_SEVERE_ERRORS)) {
          try {
            String printed;
            if (timing) {
              long startTime = System.nanoTime();
              printed = Printer.printToString(parse, printingType, printTracker, parsingTracker);
              long endTime = System.nanoTime();
              System.out.println("Printing " + fileName + " as " + Printer.getPrintingOptionName(printingType) + " took: " + Main.timeString(endTime - startTime));
            } else {
              printed = Printer.printToString(parse, printingType, printTracker, parsingTracker);
            }
            if (printed != null) {
              main.append(printed);
            }
          } catch (RecognitionException re) {
            System.out.println("Something went wrong when printing...");
          }

        } else {
          System.out.println("Not printing " + fileName + " due to parse errors.");
        }
      }


    }

    String extraParts = getExtraPartsForPrintingOption(printingType, printTracker, parsingTracker);
    outputStream.print(printStartToString(printingType, printTime, extraParts, parsingTracker));
    outputStream.print(main.toString());
    outputStream.print(printEndToString(printingType, printTime, extraParts, parsingTracker));
  }

  /*private static void printToStream(ParseResult parseResult, PrintingOption printOption, PrintingTracker printingTracker, ParsingTracker parsingTracker, PrintStream outputStream) 
  throws RecognitionException {
    System.out.println("Print to stream: " + parseResult);
    String text = printToString(parseResult, printOption, printingTracker, parsingTracker);
    if (text != null) {
      outputStream.print(text);
    }
  }*/


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

  public static String printToString(final ParseResult parseResult, final Print printingOption, final PrintingTracker printingTracker, final ParsingTracker parsingTracker) throws RecognitionException {
    //System.out.println("Printing to string...");

    if (printingOption == Print.DOT) {
      return printDotToString(parseResult);
    }

    //Normal template-based printing
    String outputText = null;
    Reader templateFile = getPrintingOptionTemplateFileReader(printingOption);
    if (templateFile != null) {
      outputText = printUsingTemplateToString(parseResult, templateFile, printingOption, printingTracker);
    } else {
      System.out.println("Sorry, printing option  " + printingOption + " not yet implemented");
    }

    return outputText;
  }

}

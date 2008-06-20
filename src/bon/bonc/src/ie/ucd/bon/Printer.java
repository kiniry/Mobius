/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.parser.BONSTTreeWalker;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.ClassDictionaryGenerator;
import ie.ucd.bon.printer.HTMLLinkGenerator;
import ie.ucd.bon.printer.PrintingTracker;
import ie.ucd.bon.printer.UnableToGenerateClassDictionaryException;
import ie.ucd.bon.typechecker.informal.SystemChartDefinition;
import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.util.Calendar;
import java.util.Collection;
import java.util.GregorianCalendar;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeNodeStream;
import org.antlr.runtime.tree.DOTTreeGenerator;
import org.antlr.runtime.tree.Tree;
import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.StringTemplateGroup;

/**
 * 
 * @author Fintan
 *
 */
public final class Printer {

  /** Prevent instantiation of Printer. */
  private Printer() { }

  public enum PrintingOption { SYSO, PLAIN_TEXT, DOT, HTML, DIC, IIG, ICG, NONE };

  private static BONSTTreeWalker walker = new BONSTTreeWalker(null);

  public static PrintingOption getPrintingOption(final String optionString) {   
    if (optionString.equalsIgnoreCase("syso") || optionString.equalsIgnoreCase("stdo")) {
      return PrintingOption.SYSO;
    } else if (optionString.equalsIgnoreCase("txt")) {
      return PrintingOption.PLAIN_TEXT;
    } else if (optionString.equalsIgnoreCase("html") || optionString.equalsIgnoreCase("xhtml")) {
      return PrintingOption.HTML;
    } else if (optionString.equalsIgnoreCase("dot")) {
      return PrintingOption.DOT;
    } else if (optionString.equalsIgnoreCase("dic")) {
      return PrintingOption.DIC;
    } else if (optionString.equalsIgnoreCase("icg")) {
      return PrintingOption.ICG;
    } else if (optionString.equalsIgnoreCase("iig")) {
      return PrintingOption.IIG;
    } else {
      return PrintingOption.NONE;
    }    
  }

  public static String getPrintingOptionName(final PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
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
      return "informal class inheritence graph";
    default:
      return "unknown"; //Shouldn't happen
    }
  }

  public static String getPrintingOptionStartString(final PrintingOption po) {
    try {
      switch(po) {
      case PLAIN_TEXT:
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

  public static String getPrintingOptionEndString(final PrintingOption po) {
    try {
      switch(po) {
      case PLAIN_TEXT:
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

  public static Reader getPrintingOptionTemplateFileReader(final PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
      return FileUtil.getResourceReader("templates/BONPlainText.stg");
    case HTML:
      return FileUtil.getResourceReader("templates/BONXHTML.stg"); 
    default:
      return null; //Shouldn't happen
    }
  }

  public static String getExtraPartsForPrintingOption(final PrintingOption po, final PrintingTracker printingTracker, final ParsingTracker parsingTracker) {
    switch(po) {
    case HTML:
      return HTMLLinkGenerator.generateLinks(printingTracker, parsingTracker);
    default:
      return "";
    }
  }

  public static boolean isFileIndependentPrintingOption(final PrintingOption po) {
    switch(po) {
    case DIC:
    case ICG:
    case IIG:
      return true;
    default:
      return false;
    }
  }

  private static String printUsingTemplateToString(final ParseResult parseResult, final Reader stFile, final PrintingOption printingOption, final PrintingTracker printingTracker) throws RecognitionException {
    try {
      StringTemplateGroup templates = new StringTemplateGroup(stFile);
      stFile.close();

      CommonTree t = (CommonTree)parseResult.getParse().getTree(); //Get input tree
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(t);  //Get stream of nodes from tree
      nodes.setTokenStream(parseResult.getTokens());

      walker.initialise(nodes, templates, printingTracker, printingOption); //Reset walker, provide inputs

      BONSTTreeWalker.prog_return r2 = walker.prog();  //Walk
      StringTemplate output = (StringTemplate)r2.getTemplate();  //Get output
      return output.toString();

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
    StringTemplate st = gen.toDOT((Tree)parseResult.getParse().getTree());
    return st.toString();
  }

  private static String printStartToString(final PrintingOption printOption, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    return formatString(getPrintingOptionStartString(printOption), printTime, extraParts, parsingTracker);
  }

  private static String printEndToString(final PrintingOption printOption, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    return formatString(getPrintingOptionEndString(printOption), printTime, extraParts, parsingTracker);
  }

  private static String formatString(final String toFormat, final Calendar printTime, final String extraParts, final ParsingTracker parsingTracker) {
    SystemChartDefinition sysDef = parsingTracker.getInformalTypingInformation().getSystem();
    String systemName = sysDef == null ? "NO SYSTEM DEFINED" : sysDef.getSystemName(); 
    return String.format(toFormat, 
        printTime, 
        Main.getVersion(), 
        systemName,
        extraParts
    );
  }


  public static void printToStream(final Collection<File> files, final ParsingTracker parsingTracker, final PrintStream outputStream, final PrintingOption printingOption, final boolean printToFile, final boolean timing) {
    Main.logDebug("Printing to stream.");
    Calendar printTime = new GregorianCalendar();
    PrintingTracker printTracker = new PrintingTracker();
    StringBuilder main = new StringBuilder();


    if (isFileIndependentPrintingOption(printingOption)) {
      main.append(printFileIndependentPrintingOptionToString(printingOption, parsingTracker));
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
              printed = Printer.printToString(parse, printingOption, printTracker, parsingTracker);
              long endTime = System.nanoTime();
              System.out.println("Printing " + fileName + " as " + Printer.getPrintingOptionName(printingOption) + " took: " + Main.timeString(endTime - startTime));
            } else {
              printed = Printer.printToString(parse, printingOption, printTracker, parsingTracker);
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

    String extraParts = getExtraPartsForPrintingOption(printingOption, printTracker, parsingTracker);
    outputStream.print(printStartToString(printingOption, printTime, extraParts, parsingTracker));
    outputStream.print(main.toString());
    outputStream.print(printEndToString(printingOption, printTime, extraParts, parsingTracker));
  }

  /*private static void printToStream(ParseResult parseResult, PrintingOption printOption, PrintingTracker printingTracker, ParsingTracker parsingTracker, PrintStream outputStream) 
  throws RecognitionException {
    System.out.println("Print to stream: " + parseResult);
    String text = printToString(parseResult, printOption, printingTracker, parsingTracker);
    if (text != null) {
      outputStream.print(text);
    }
  }*/


  private static String printFileIndependentPrintingOptionToString(final PrintingOption printingOption, final ParsingTracker parsingTracker) {
    switch (printingOption) {
    case DIC:
      return printGeneratedClassDictionaryToString(parsingTracker);
    case ICG:
      return Grapher.graphInformalClusterContainment(parsingTracker);
    case IIG:
      return Grapher.graphInformalClassInheritence(parsingTracker);
    default:
      return "";
    }
  }

  public static String printToString(final ParseResult parseResult, final PrintingOption printingOption, final PrintingTracker printingTracker, final ParsingTracker parsingTracker) throws RecognitionException {
    System.out.println("Printing to string...");

    if (printingOption == PrintingOption.DOT) {
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

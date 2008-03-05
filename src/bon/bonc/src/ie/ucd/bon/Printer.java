/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.parser.BONSTTreeWalker;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.HTMLLinkGenerator;
import ie.ucd.bon.printer.PrintingTracker;
import ie.ucd.bon.typechecker.informal.SystemChartDefinition;
import ie.ucd.bon.util.FileUtil;

import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.util.Calendar;
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
public class Printer {

  public enum PrintingOption { SYSO, PLAIN_TEXT, DOT, HTML, NONE };
  
  private static BONSTTreeWalker walker = new BONSTTreeWalker(null);

  public static PrintingOption getPrintingOption(String optionString) {   
    if (optionString.equalsIgnoreCase("syso") || optionString.equalsIgnoreCase("stdo")) {
      return PrintingOption.SYSO;
    } else if (optionString.equalsIgnoreCase("txt")) {
      return PrintingOption.PLAIN_TEXT;
    } else if (optionString.equalsIgnoreCase("html") || optionString.equalsIgnoreCase("xhtml")) {
      return PrintingOption.HTML;
    } else if (optionString.equalsIgnoreCase("dot")) {
      return PrintingOption.DOT;
    } else {
      return PrintingOption.NONE;
    }    
  }
  
  public static String getPrintingOptionName(PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
      return "plain-text";
    case HTML:
      return "web-page format";
    case DOT:
      return ".dot graph format";
    default:
      return "unknown"; //Shouldn't happen
    }
  }

  public static String getPrintingOptionStartString(PrintingOption po) {
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
  
  public static String getPrintingOptionEndString(PrintingOption po) {
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
  
  public static Reader getPrintingOptionTemplateFileReader(PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
      return FileUtil.getResourceReader("templates/BONPlainText.stg");
    case HTML:
      return FileUtil.getResourceReader("templates/BONXHTML.stg"); 
    default:
      return null; //Shouldn't happen
    }
  }
  
  public static String getExtraPartsForPrintingOption(PrintingOption po, PrintingTracker printingTracker, ParsingTracker parsingTracker) {
    switch(po) {
    case HTML:
      return HTMLLinkGenerator.generateLinks(printingTracker, parsingTracker);
    default:
      return "";
    }
  }

  private static String printUsingTemplateToString(ParseResult parseResult, Reader stFile, PrintingOption printingOption, PrintingTracker printingTracker) throws RecognitionException {
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

  public static String printDotToString(ParseResult parseResult) {
    DOTTreeGenerator gen = new DOTTreeGenerator();
    StringTemplate st = gen.toDOT((Tree)parseResult.getParse().getTree());
    return st.toString();
  }

  private static void printStartToStream(PrintingOption printOption, PrintStream outputStream, Calendar printTime, String extraParts, ParsingTracker parsingTracker) {
    String startString = formatString(getPrintingOptionStartString(printOption), printTime, extraParts, parsingTracker);
    outputStream.print(startString);
  }
  
  private static void printEndToStream(PrintingOption printOption, PrintStream outputStream, Calendar printTime, String extraParts, ParsingTracker parsingTracker) {
    String endString = formatString(getPrintingOptionEndString(printOption), printTime, extraParts, parsingTracker);
    outputStream.print(endString);
  }
  
  private static String formatString(String toFormat, Calendar printTime, String extraParts, ParsingTracker parsingTracker) {
    SystemChartDefinition sysDef = parsingTracker.getInformalTypingInformation().getSystem();
    String systemName = sysDef == null ? "NO SYSTEM DEFINED" : sysDef.getSystemName(); 
    return String.format(toFormat, 
        printTime, 
        Main.getVersion(), 
        systemName,
        extraParts
        );
  }

  public static void printToStream(ParseResult parseResult, PrintingOption printOption, PrintingTracker printingTracker, ParsingTracker parsingTracker, PrintStream outputStream) 
  throws RecognitionException {
    String text = printToString(parseResult, printOption, printingTracker);
    if (text != null) {
      Calendar printTime = new GregorianCalendar();
      
      String extraParts = getExtraPartsForPrintingOption(printOption, printingTracker, parsingTracker);
      
      printStartToStream(printOption, outputStream, printTime, extraParts, parsingTracker);
      outputStream.println(text);
      printEndToStream(printOption, outputStream, printTime, extraParts, parsingTracker);
      
    }
  }
  
  public static String printToString(ParseResult parseResult, PrintingOption printingOption, PrintingTracker printingTracker) throws RecognitionException {
    String outputText = null;
    
    if (printingOption == PrintingOption.DOT) {
      outputText = printDotToString(parseResult);
    } else {
      Reader templateFile = getPrintingOptionTemplateFileReader(printingOption);
      if (templateFile != null) {
        outputText = printUsingTemplateToString(parseResult, templateFile, printingOption, printingTracker);
      } else {
        System.out.println("Sorry, printing option  " + printingOption + " not yet implemented");
      }
    }    
    return outputText;
  }

}

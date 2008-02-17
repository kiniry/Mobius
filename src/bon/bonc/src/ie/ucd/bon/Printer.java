/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

//import ie.ucd.ebon.parser.EBONPrinterTreeWalker;
import ie.ucd.bon.parser.BONSTTreeWalker;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.net.URISyntaxException;
import java.util.Collection;
import java.util.HashSet;

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
    if (optionString.equals("syso")) {
      return PrintingOption.SYSO;
    } else if (optionString.equals("txt")) {
      return PrintingOption.PLAIN_TEXT;
    } else if (optionString.equals("html")) {
      return PrintingOption.HTML;
    } else if (optionString.equals("dot")) {
      return PrintingOption.DOT;
    } else {
      return PrintingOption.NONE;
    }    
  }
  
  public static String getPrintingOptionName(PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
      return "plain-text";
    case DOT:
      return ".dot graph format";
    default:
      return "unknown"; //Shouldn't happen
    }
  }

  public static String getPrintingOptionFileSuffix(PrintingOption po) {
    switch(po) {
    case PLAIN_TEXT:
      return ".bon";
    case DOT:
      return ".dot";
    case HTML:
      return ".html";
    default:
      return ".unknown"; //Shouldn't happen
    }
  }

  public static Reader getPrintingOptionTemplateFileReader(PrintingOption po) {

    switch(po) {
    case PLAIN_TEXT:
      return FileUtil.getResourceReader("templates/EBONPlainText.stg");
    default:
      return null; //Shouldn't happen
    }

  }

  public static String getPrintingOptionFileName(String originalFileName, PrintingOption po) { 
    return originalFileName + getPrintingOptionFileSuffix(po);
  }

  public static String getPrintingOptionFileName(String originalFileName, PrintingOption po, File outputDirectory) {
    return outputDirectory.getAbsolutePath() + File.separatorChar + getPrintingOptionFileName(originalFileName, po);    
  }

  public static Collection<PrintingOption> getPrintingOptionsList(String optionListString, String separator) {
    String[] parts = optionListString.split(separator);
    HashSet<PrintingOption> printingOptionsSet = new HashSet<PrintingOption>();
    for (String p : parts) {
      PrintingOption po = getPrintingOption(p);
      if (po != PrintingOption.NONE) {
        printingOptionsSet.add(po);
      } else {
        //Print error - unknown printing option?
      }
    }
    return printingOptionsSet;
  }

  public static String printToString(ParseResult parseResult, Reader stFile) throws RecognitionException {
    try {
      //FileReader groupFileR = new FileReader(stFile); //Read the string-template file
      StringTemplateGroup templates = new StringTemplateGroup(stFile);
      //groupFileR.close();
      stFile.close();
      
      CommonTree t = (CommonTree)parseResult.getParse().getTree(); //Get input tree
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(t);  //Get stream of nodes from tree
      nodes.setTokenStream(parseResult.getTokens());

      walker.initialise(nodes, templates); //Reset walker, provide inputs

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

  public static void printToFile(ParseResult parseResult, File outputDirectory, PrintingOption printingOption) 
  throws RecognitionException {
    
    String outputFilename = outputDirectory.getAbsolutePath() + File.separatorChar + parseResult.getFileName() + getPrintingOptionFileSuffix(printingOption);
    String outputText = null;
    
    if (printingOption == PrintingOption.DOT) {
      outputText = printDotToString(parseResult);
    } else {
      Reader templateFile = getPrintingOptionTemplateFileReader(printingOption);
      if (templateFile != null) {
        outputText = printToString(parseResult, templateFile);
      } else {
        System.out.println("Sorry, printing option  " + printingOption + " not yet implemented");
      }
    }
    
    try {
      if (outputText != null) {
        PrintStream out = new PrintStream(outputFilename);
        out.print(outputText);
        out.close();
        System.out.println("Succesfully created: " + outputFilename);
      }
    } catch (IOException ioe) {
      System.out.println("Error writing to file " + outputFilename);
    }

  }

  public static void prettyPrintToStream(ParseResult parseResult, PrintStream outputStream) 
  throws RecognitionException {
    String text = printToString(parseResult, getPrintingOptionTemplateFileReader(PrintingOption.PLAIN_TEXT));
    System.out.println(text);
  }

}

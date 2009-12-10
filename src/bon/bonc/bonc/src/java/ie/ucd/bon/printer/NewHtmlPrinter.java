/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ContractClause;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.template.FreeMarkerTemplate;
import ie.ucd.bon.typechecker.BONST;
import ie.ucd.bon.util.ExecUtil;
import ie.ucd.bon.util.FileUtil;
import ie.ucd.bon.util.KeyPair;
import ie.ucd.bon.util.STUtil;
import ie.ucd.bon.util.StringUtil;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public class NewHtmlPrinter {

  /** Paths of files to copy.  */
  private final static String[] filePaths = { "js/jquery/jquery-1.3.2.js", "js/jquery/jquery.history.js",
    "js/jquery/jquery.hotkeys.js", "js/scripty/scriptaculous.js",
    "js/scripty/prototype.js", "js/scripty/builder.js",
    "js/scripty/controls.js", "js/scripty/dragdrop.js",
    "js/scripty/effects.js", "js/scripty/slider.js",
    "js/scripty/sound.js", "js/scripty/unittest.js",
    "style.css", "js/jdoc.js",
    "js/sh/shCore.js", "js/sh/shCore.css", "js/sh/shThemeDefault.css",
    "js/sh/shThemeEclipse.css", "js/sh/shBrushBON.js"     
  };
  /** Dirs that need to be created. */
  private final static String[] dirs = {"js", "js/scripty", "js/scripty2", "js/jquery", "js/sh"};

  private final File outputDirectory;
  private final ParsingTracker tracker;
  private final BONST st;
  private final boolean compileImages;
  private final Map<String,Object> map;

  private BONPrintMonitor monitor;
  
  private final ExecUtil exec;
  
  public NewHtmlPrinter(File outputDirectory, ParsingTracker tracker, boolean compileImages) {
    this.outputDirectory = outputDirectory;
    this.tracker = tracker;
    this.st = tracker.getSymbolTable();
    this.compileImages = compileImages;
    this.map = prepareMap();
    
    exec = ExecUtil.instance;
  }

  public void print(BONPrintMonitor monitor) {
    this.monitor = monitor;
    
    int work = getTotalWork();
    monitor.begin("Generating BON html documentation", work);
    
    //TODO copy relevant javascript files
    monitor.setInfo("Doing new html printing " + outputDirectory);
    
    if (!setupOutputDirectory()) {
      monitor.finishWithErrorMessage("Unable to setup files in " + outputDirectory);
      return;
    }

    if (monitor.isCancelled()) {
      return;
    }
    
    printAllImageLatex();
    
    if (monitor.isCancelled()) {
      return;
    }
    
    boolean imagesCompiled = compileImages && buildImages();
    
    if (monitor.isCancelled()) {
      return;
    }
    
    //JS gen
    FreeMarkerTemplate.writeTemplateToFile(relativeFile("js/vars.js"), "newhtml/vars.ftl", map);

    //Index page
    FreeMarkerTemplate.writeTemplateToFile(relativeFile("index.html"), "newhtml/index.ftl", map);
    FreeMarkerTemplate.writeTemplateToFile(relativeFile("all-classes.html"), "newhtml/all-classes.ftl", map);

    //Classes
    for (Clazz clazz : st.classes.values()) {
      monitor.setInfo("Generating html for " + clazz.name.name);
      printForClass(clazz);
      monitor.progress(1);
      if (monitor.isCancelled()) {
        return;
      }
    }

    //Clusters
    //TODO print clusters
    
    
    if (!imagesCompiled) {
      File script = relativeFile("make-images.sh");
      if (FileUtil.copyResourceToExternalFile("templates/newhtml/" + "make-images.sh", script)) {
        if (script.getParent().equals("")) {
          System.out.println("Execute \"bash " + script + "\" to build the images.");
        } else {
          System.out.println("Execute \"cd " + script.getParent() + "; bash " + script.getName() + "\" to build the images.");
        }
      }
    }
    
    monitor.complete();
  }

  private void printAllImageLatex() {
    monitor.setInfo("Generating latex source");
    for (Clazz clazz : st.classes.values()) {
      monitor.setInfo("Generating latex for " + clazz.name.name);
      printClassImageLatex(clazz);
      monitor.progress(1);
      if (monitor.isCancelled()) {
        return;
      }
    }
  }

  private void printClassImageLatex(Clazz clazz) {
    prepareMapForClass(clazz);
    
    map.put("diagram", StringUtil.latexPrint(clazz));
    FreeMarkerTemplate.writeTemplateToFile(relativeFile(clazz.name.name + "-diagram.tex"), "newhtml/tikz.ftl", map);
    
    for (KeyPair<String,FeatureSpecification> pair : st.featuresMap.getAllPairs(clazz)) {
      String featureName = pair.a;
      FeatureSpecification fSpec = pair.b;
      ContractClause contracts = fSpec.contracts;
      int count = 1;
      for (Expression pre : contracts.preconditions) {
        map.put("equation", StringUtil.latexPrint(pre) + ";");
        FreeMarkerTemplate.writeTemplateToFile(relativeFile(STUtil.getFeatureSignature(featureName, fSpec, clazz, st) + "-precondition" + count + ".tex"), "newhtml/equation.ftl", map);
        count++;
      }
      count = 1;
      for (Expression post : contracts.postconditions) {
        map.put("equation", StringUtil.latexPrint(post) + ";");
        FreeMarkerTemplate.writeTemplateToFile(relativeFile(STUtil.getFeatureSignature(featureName, fSpec, clazz, st) + "-postcondition" + count + ".tex"), "newhtml/equation.ftl", map);
        count++;
      }
    }

    if (clazz.classInterface != null) {
      int count = 1;
      for (Expression inv : clazz.classInterface.invariant) {
        map.put("equation", StringUtil.latexPrint(inv) + ";");
        FreeMarkerTemplate.writeTemplateToFile(relativeFile(clazz.name.name + "-invariant" + count + ".tex"), "newhtml/equation.ftl", map);
        count++;
      }
    }
  }

  private void prepareMapForClass(Clazz clazz) {
    map.put("class", clazz);
    map.put("qualifiedclass", STUtil.getQualifiedClassString(clazz.name.name, st));
    if (clazz.classInterface != null) {
      map.put("parents", clazz.classInterface.parents);
      map.put("features", st.featuresMap.getAll(clazz));
    } else {
      map.put("parents", null);
      map.put("features", null);
    }
  }

  private void printForClass(Clazz clazz) {
    prepareMapForClass(clazz);
    map.put("children", STUtil.getAllDescendants(clazz, st));
    FreeMarkerTemplate.writeTemplateToFile(relativeFile(clazz.name.name + ".html"), "newhtml/fclass.ftl", map);
    map.put("related", getRelated(clazz));
    FreeMarkerTemplate.writeTemplateToFile(relativeFile(clazz.name.name + "-related.html"), "newhtml/fclass-related.ftl", map);

    FreeMarkerTemplate.writeTemplateToFile(relativeFile(clazz.name.name + "-diagram.html"), "newhtml/fclass-diagram.ftl", map);
  }

  private boolean setupOutputDirectory() {
    for (String dir : dirs) {
      if (!checkDirectory(dir)) {
        return false;
      }
    }

    for (String path : filePaths) {
      if (!FileUtil.copyResourceToExternalFile("templates/newhtml/" + path, relativeFile(path))) {
        return false;
      }
    }
    return true;
  }

  private boolean checkDirectory(String relativePath) {
    return checkDirectory(relativeFile(relativePath));
  }

  private boolean checkDirectory(File directory) {
    if (directory.exists()) {
      if (!directory.isDirectory()) {
        monitor.finishWithErrorMessage(directory.getPath() + " exists and is not a directory.");
        return false;
      }
    } else {
      if (!directory.mkdir()) {
        monitor.finishWithErrorMessage("Unable to make directory " + directory.getPath());
        return false;
      }
    }
    return true;
  }

  private File relativeFile(String path) {
    return relativeFile(outputDirectory, path);
  }

  private File relativeFile(File file, String path) {
    String start = file.getPath();
    if (!start.endsWith("/")) {
      start += '/';
    }
    return new File(start + path);
  }

  private Map<String,Object> prepareMap() {
    Map<String,Object> map = new HashMap<String,Object>();

    map.put("tracker", tracker);
    BONST st = tracker.getSymbolTable();
    map.put("st", st);

    map.put("fclasses", STUtil.alphabeticalClasses(st));
    map.put("fclusters", st.clusters.values());
    map.put("iclasses", st.informal.classes.values());
    map.put("iclusters", st.informal.clusters.values());

    map.put("outputDir", outputDirectory);
    map.put("outputDirPath", outputDirectory.getPath().endsWith(File.separator) ? outputDirectory.getPath() : outputDirectory.getPath() + File.separator);

    return map;
  }

  private Collection<Clazz> getRelated(Clazz clazz) {
    //TODO other classes in cluster, classes that use this class
    Set<Clazz> related = new LinkedHashSet<Clazz>();
    //Children
    related.addAll(STUtil.getAllDescendants(clazz, st));
    //All parents
    related.addAll(STUtil.getAllAncestors(clazz, st));

    if (clazz.classInterface != null) {
      //Features
      for (FeatureSpecification fs : st.featuresMap.getAll(clazz)) {
        if (fs.hasType != null) {
          String rt = fs.hasType.type.identifier;
          if (!rt.equals("Void")) {
            related.add(st.classes.get(rt));
          }
        }
        for (FeatureArgument fa : fs.arguments) {
          related.add(st.classes.get(fa.type.identifier));
        }
      }
    }
    related.remove(null);
    return related;
  }

  private boolean buildImages() {
    if (!checkTools()) {
      return false;
    }
    
    if (monitor.isCancelled()) {
      return false;
    }

    if (!compileLatex()) {
      return false;
    }
    
    if (monitor.isCancelled()) {
      return false;
    }

    if (!resizeAndConvertImage()) {
      return false;
    }
    
    if (monitor.isCancelled()) {
      return false;
    }

    monitor.setInfo("Cleaning up.");
    FileUtil.deleteAll(outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".pdf")));
    FileUtil.deleteAll(outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".tex")));
    FileUtil.deleteAll(outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".log")));
    FileUtil.deleteAll(outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".aux")));
    
    return true;
  }

  private boolean checkTools() {
    if (!exec.hasBinaryOnPath("gm")) {
      monitor.finishWithErrorMessage("It doesn't look like GraphicsMagick (gm) is installed and on the system path.");
      return false;
    }
    if (!exec.hasBinaryOnPath("rubber")) {
      monitor.finishWithErrorMessage("It doesn't look like rubber is installed and on the system path.");
      return false;
    }
    if (!exec.hasBinaryOnPath("pdfcrop")) {
      monitor.finishWithErrorMessage("It doesn't look like pdfcrop is installed and on the system path.");
      return false;
    }
    return true;
  }

  private boolean resizeAndConvertImage() {
    File[] pdfFiles = outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".pdf"));
    for (File pdfFile : pdfFiles) {
      String pdfFilePath = pdfFile.getPath();
      monitor.setInfo("Resizing " + pdfFile.getName());
      if (exec.execWaitIgnoreOutput("pdfcrop " + pdfFilePath + " " + pdfFilePath) != 0) {
        monitor.finishWithErrorMessage("Error resizing " + pdfFile.getName());
        return false;
      }
      monitor.progress(1);
      if (monitor.isCancelled()) {
        return false;
      }
      monitor.setInfo("Converting " + pdfFile.getName() + " to png");
      if (exec.execWaitIgnoreOutput("gm convert -scale 15%x15% -density 1000 -transparent #FFFFFF " + pdfFilePath + " " + pdfFilePath.substring(0,pdfFilePath.length()-3).concat("png")) != 0) {
        monitor.finishWithErrorMessage("Error converting " + pdfFile.getName());
        return false;
      }
      monitor.progress(1);
      if (monitor.isCancelled()) {
        return false;
      }
    }
    return true;
  }

  private boolean compileLatex() {
    monitor.setInfo("Compiling latex...");
    File[] texFiles = outputDirectory.listFiles(FileUtil.getSuffixFilenameFilter(".tex"));
    //String filesString = StringUtil.appendWithSeparator(texFiles, " ", false);
    for (File file : texFiles) {
      monitor.setInfo("Compiling latex " + file);
      if (exec.execWaitIgnoreOutput("rubber -d --inplace " + file) != 0) {
        monitor.finishWithErrorMessage("Error compiling latex");
        return false;
      }
      monitor.progress(1);
      if (monitor.isCancelled()) {
        return false;
      }
    }
    monitor.setInfo("Done compiling latex...");
    return true;
  }
  
  private int getTotalWork() {
    //Count one for each class html
    int count = st.classes.values().size();
    //Count 4 for each latex file (print, compile, resize, convert)
    count += 4 * getNumLatexFiles();
    
    return count;
  }
  
  private int getNumLatexFiles() {
    int count = st.classes.size(); //1 diagram per class
    for (Clazz clazz : st.classes.values()) {
      for (KeyPair<String,FeatureSpecification> pair : st.featuresMap.getAllPairs(clazz)) {
        count += pair.b.contracts.preconditions.size() + pair.b.contracts.postconditions.size();
      }
      if (clazz.classInterface != null) {
        count += clazz.classInterface.invariant.size();
      }
    }
    return count;
  }

}

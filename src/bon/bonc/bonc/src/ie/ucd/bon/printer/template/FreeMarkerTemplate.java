/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer.template;

import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;

import freemarker.template.Configuration;
import freemarker.template.TemplateException;

public class FreeMarkerTemplate {

  private static Configuration config;
  private final Map<String,Object> dataModel;

  public FreeMarkerTemplate() {
    dataModel = new HashMap<String,Object>();
  }

  public FreeMarkerTemplate addToDataModel(String name, Object o) {
    dataModel.put(name, o);
    return this;
  }

  public void writeTemplate(Writer out, String templateName) {
    writeTemplate(out, templateName, dataModel);
  }

  private static Configuration getConfig() {
    if (config == null) {
      config = new Configuration();
      config.setClassForTemplateLoading(FileUtil.class, "/templates/");
    }
    return config;
  }

  public static boolean writeTemplate(Writer out, String templateName, Map<String,Object> dataModel) {
    try {
      dataModel.put("prepareManifest", new PrepareManifestForXHTMLMethod());
      dataModel.put("pp", new PrettyPrintMethod());
      getConfig().getTemplate(templateName).process(dataModel, out);
      out.flush();
      return true;
    } catch (IOException e) {
      e.printStackTrace();
      return false;
    } catch (TemplateException e) {
      e.printStackTrace();
      return false;
    }
  }

  public static boolean writeTemplateToFile(File outputFile, String templateName, Map<String,Object> dataModel) {
    try {
      FileWriter fw = new FileWriter(outputFile);
      if (!writeTemplate(fw, templateName, dataModel)) {
        return false;
      } else {
        fw.close();
        return true;
      }
    } catch (IOException e) {
      e.printStackTrace();
      return false;
    }
  }
  
}

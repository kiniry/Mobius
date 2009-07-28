package jml2bml;

import java.io.PrintWriter;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import com.sun.tools.javac.file.ZipArchive.ZipFileObject;

public class JmlDiagnosticListener implements DiagnosticListener < JavaFileObject >{
  
  private final PrintWriter writer;
  private final boolean ignoreSpecsErrors;

  public JmlDiagnosticListener(final PrintWriter writer) {
    this.writer = writer;
    this.ignoreSpecsErrors = true;
  }
  
  public JmlDiagnosticListener(final PrintWriter writer, boolean ignoreSpecsErrors) {
    this.writer = writer;
    this.ignoreSpecsErrors = ignoreSpecsErrors;
  }
  
  private boolean isJmlSpecs(final JavaFileObject jfo) {
    if (jfo instanceof ZipFileObject) {
      ZipFileObject zfo = (ZipFileObject) jfo;
      if (zfo.getZipName().endsWith("jmlspecs.jar"))
          return true;
    }
    return false;
  }

  public void report(Diagnostic < ? extends JavaFileObject > diagnostic) {
    JavaFileObject j = diagnostic.getSource();
    if (ignoreSpecsErrors && isJmlSpecs(j)) return;
    writer.println(diagnostic.toString());
    writer.flush();
  }
}

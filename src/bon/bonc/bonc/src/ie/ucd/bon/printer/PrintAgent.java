package ie.ucd.bon.printer;

import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.source.SourceLocation;

import java.io.IOException;
import java.util.List;
import java.util.Map;

public interface PrintAgent {

  void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc);

  String getAllOutputAsString(ParsingTracker tracker, Map<String,Object> additionalData) throws IOException;
}

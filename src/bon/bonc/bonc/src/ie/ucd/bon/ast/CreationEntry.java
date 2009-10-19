
/**
  This class is generated automatically from normal_classes.tpl.
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class CreationEntry extends AstNode {


  public final ClassName name;

  public final List<String> types;


  // === Constructors and Factories ===
  protected CreationEntry(ClassName name, List<String> types, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.types = types; assert types != null;
  }

  public static CreationEntry mk(ClassName name, List<String> types, SourceLocation location) {
    return new CreationEntry(name, types, location);
  }

  // === Accessors ===

  public ClassName getName() { return name; }
  public List<String> getTypes() { return types; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitCreationEntry(this, name, types, getLocation());
  }

  // === Others ===
  @Override
  public CreationEntry clone() {
    ClassName newName = name == null ? null : name.clone();
    List<String> newTypes = types;
    return CreationEntry.mk(newName, newTypes, getLocation());
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CreationEntry ast node: ");
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
        sb.append("types = ");
    sb.append(types);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}


/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.errors;

import ie.ucd.bon.parser.SourceLocation;

public class MissingElementParseError extends ParsingError {

  private static final String message1 = "Missing %s";
  private static final String message2 = "Missing %s %s";
  
  private final String elementName;
  private final String locationDescription;
  
  public MissingElementParseError(SourceLocation sourceLoc, String elementName, String locationDescription, boolean isSevere) {
    super(sourceLoc, isSevere);
    this.elementName = elementName;
    this.locationDescription = locationDescription;
  }

  @Override
  public String getMessage() {
    if (locationDescription == null) {
      return String.format(message1, elementName);
    } else {
      return String.format(message2, elementName, locationDescription);
    }
  }
  
}

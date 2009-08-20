package ie.ucd.autograder.util;

import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.util.Pair.MarkGradePair;

import java.util.ArrayList;
import java.util.List;

public class Util {

  public static List<MarkGradePair> convertStringPropertyToMarkGradePairs(String propertyValue) {
    String[] pairs = propertyValue.split(";");
    List<MarkGradePair> result = new ArrayList<MarkGradePair>(pairs.length);

    for (String pair : pairs) {

      String[] parts = pair.split(",");
      if (parts.length == 2) {
        try {
          Double mark = Double.valueOf(parts[1]);
          Grade grade = Grade.gradeFromStringName(parts[0]);
          result.add(new MarkGradePair(mark, grade));
        } catch (NumberFormatException e) {
          //TODO throw error
        }
      } else {
        //TODO throw error
      }
    }

    return result;
  }

}

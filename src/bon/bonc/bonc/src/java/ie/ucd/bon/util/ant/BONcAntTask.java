package ie.ucd.bon.util.ant;

import ie.ucd.bon.API;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.taskdefs.MatchingTask;
import org.apache.tools.ant.types.resources.FileResource;

public class BONcAntTask extends MatchingTask {
  
  private boolean checkInformal = true;
  private boolean checkFormal = true;
  private boolean typeCheck = true;
  private boolean checkConsistency = true;
  
  @Override
  public void init() throws BuildException {
    super.setTaskName("bonc");
  }

  @Override
  public void execute() throws BuildException {  
    List<File> files = new ArrayList<File>(fileset.size());
    
    Iterator<?> iterator = fileset.iterator();
    while (iterator.hasNext()) {
      FileResource fr = (FileResource)iterator.next();
      files.add(fr.getFile());
    }
    
    ParsingTracker tracker = API.parse(files);
    if (tracker.continueFromParse() && typeCheck) {
      API.typeCheck(tracker, checkInformal, checkFormal, checkConsistency, typeCheck, false);
    }
    
    //TODO print issues, throw BuildException (if necessary)
  }

  public void setCheckInformal(boolean checkInformal) {
    this.checkInformal = checkInformal;
  }

  public void setCheckFormal(boolean checkFormal) {
    this.checkFormal = checkFormal;
  }

  public void setTypeCheck(boolean typeCheck) {
    this.typeCheck = typeCheck;
  }

  public void setCheckConsistency(boolean checkConsistency) {
    this.checkConsistency = checkConsistency;
  }

  
  
}

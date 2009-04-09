/*
 *
 * Copyright (C) 2005  brad kyer b.kyer _at_ hydrogenline.com
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package org.apache.tools.ant.taskdefs;

import org.apache.tools.ant.Task;
import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Project;
import org.apache.tools.ant.types.Commandline;
import org.apache.tools.ant.util.FileUtils;
import java.io.File;
import java.io.IOException;

// diff file generation
import bmsi.util.DiffPrint;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.FileWriter;

/**
 * Diffs a file "to" by comparing another file "from" to it;
 * on the execution path.
 * @author Brad G. Kyer
 *         <a href="mailto:b.kyer _at_ hydrogenline.com">b.kyer _at_ hydrogenline.com</a>
 *
 * @version $Revision: 1.0.0 $
 *
 * @since Ant 1.5.1
 *
 * @ant.task category="utility"
 */
public class Diff extends Task {

    private File toFile;
    private File fromFile;
    private File diffFile;
    private String diffType = "-c";
    
    /**
     * The file to diff to;
     */
    public void setTofile(File file) {
        toFile = file;
        if (!file.exists()) {
            throw new BuildException("Diff toFile " + file + " doesn\'t exist", 
                                     location);
        }
    }

    /**
     * The file to diff from;
     */
    public void setFromfile(File file) {
        fromFile = file;
        if (!file.exists()) {
            throw new BuildException("Diff fromFile " + file + " doesn\'t exist", 
                                     location);
        }
    }

    /**
     * The output dir for diff;
     */
    public void setDifffile(File file) {
        diffFile = file;
    }

    /**
     * The diff output type;
     */
    public void setDifftype(String aType) {
        diffType = MergeDiffHelper.checkDiffType(aType);
    }

    /**
     * execute diff
     * @throws BuildException when it all goes a bit pear shaped
     */
    public void execute() throws BuildException {

        log("Beginning diff", Project.MSG_VERBOSE);

        try {

            log("Diff file " + fromFile.getAbsolutePath() + " to " + toFile.getAbsolutePath());

            String[] myStrings = new String[3];
            myStrings[0] = diffType;
            myStrings[1] = toFile.getPath();
            myStrings[2] = fromFile.getPath();
                        
            StringWriter myStringWriter = new StringWriter();
            PrintWriter  myWriter       = new PrintWriter(myStringWriter);
            DiffPrint    myDiffPrint    = new DiffPrint();
            myDiffPrint.doWork(myStrings, myWriter);

            myWriter.flush();
            myWriter.close();
            String myDiff = myStringWriter.toString();

            if(myDiff.length() > 0) {

                log("Merge output " + myDiff, Project.MSG_DEBUG);

                FileUtils myFileUtils =   FileUtils.newFileUtils();

                if(diffFile == null) {
                    diffFile = myFileUtils.createTempFile(toFile.getName() + "_-", ".diff", new File("."));
                }

                File      myDiffFile  = diffFile;

                log("Differences found, results in " + myDiffFile.getAbsolutePath());

                
                FileWriter myFileWriter = new FileWriter(myDiffFile);
                myFileWriter.write(myDiff);
                myFileWriter.flush();
                myFileWriter.close();
                myFileWriter = null;
            }

        } catch (IOException e) {
            throw new BuildException(e, location);
        }
    }

}// Diff

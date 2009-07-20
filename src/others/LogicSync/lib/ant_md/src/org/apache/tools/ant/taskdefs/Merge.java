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
import org.apache.tools.ant.DirectoryScanner;
import org.apache.tools.ant.types.FileSet;
import org.apache.tools.ant.types.Mapper;
import org.apache.tools.ant.types.FilterChain;
import org.apache.tools.ant.types.FilterSet;
import org.apache.tools.ant.types.FilterSetCollection;
import org.apache.tools.ant.util.FileUtils;
import org.apache.tools.ant.util.FileNameMapper;
import org.apache.tools.ant.util.FlatFileNameMapper;
import org.apache.tools.ant.util.IdentityMapper;
import org.apache.tools.ant.util.SourceFileScanner;

// diff file generation
import bmsi.util.DiffPrint;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.FileWriter;

// used to manage diff files
import java.io.File;
import java.io.IOException;
import java.util.Vector;
import java.util.Hashtable;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;

/**
 * Merges a "to" file or directory from an alternative "from" file
 * or directory.  Files are only merged if the "to" file is newer
 * than the "from" file (unless forcediff is true), or when the "to"
 * file does not exist.  It is possible to generate bad merge files.</p>
 *
 *
 * @author Brad G. Kyer
 *         <a href="mailto:b.kyer _at_ hydrogenline.com">b.kyer _at_ hydrogenline.com</a>
 *
 * @version $Revision: 1.0.0 $
 *
 * @since Ant 1.5.1
 *
 * @ant.task category="utility"
 */
public class Merge extends Task {
    protected File file = null;     // the source file
    protected File destFile = null; // the destination file
    protected File destDir = null;  // the destination directory
    protected File diffDir = null;  // the diff output directory
    private String diffType = "-c";

    protected Vector filesets = new Vector();

    protected boolean filtering = false;
    protected int verbosity = Project.MSG_VERBOSE;
    protected boolean includeEmpty = true;
    private boolean failonerror = true;
    private boolean forcediff = false;
    private boolean flatten = false;

    protected Hashtable fileCopyMap = new Hashtable();
    protected Hashtable dirCopyMap = new Hashtable();
    protected Hashtable completeDirMap = new Hashtable();

    protected Mapper mapperElement = null;
    private Vector filterChains = new Vector();
    private Vector filterSets = new Vector();
    private FileUtils fileUtils;
    private String encoding = null;

    // for patch
    private boolean ignorewhitespace = false;
    private int     strip            = -1;
    private boolean quiet            = false;
    private boolean reverse          = false;
    private boolean backups          = false;

    /**
     * Merge task constructor. 
     */
    public Merge() {
        fileUtils = FileUtils.newFileUtils();
    }

    protected FileUtils getFileUtils() {
        return fileUtils;
    }

    /**
     * Sets a single "from" source file to merge.
     */
    public void setFromfile(File file) {
        this.file = file;
    }

    /**
     * Sets the "to" file.
     */
    public void setTofile(File destFile) {
        this.destFile = destFile;
    }

    /**
     * Sets the destination directory.
     */
    public void setTodir(File destDir) {
        this.destDir = destDir;
    }

    /**
     * Sets the merge output directory.
     */
    public void setDiffdir(File diffDir) {
        this.diffDir = diffDir;
    }

    /**
     * Force diff between from and to (ignore timestamps); optional, default=false
     */
    public void setForcediff(boolean f) {
        forcediff = f;
    }

    /**
     * The diff output type;
     */
    public void setDifftype(String aType) {
        diffType = MergeDiffHelper.checkDiffType(aType);
    }

    /**
     * flag to create backups; optional, default=false
     */
    public void setBackups(boolean b) {
        backups = b;
    }

    /**
     * flag to ignore whitespace differences; default=false
     */
    public void setIgnorewhitespace(boolean ignore) {
        ignorewhitespace = ignore;
    }

    /**
     * Strip the smallest prefix containing <i>num</i> leading slashes
     * from filenames.
     *
     * <p>patch's <i>-p</i> option.
     * @param num number of lines to strip
     */
    public void setStrip(int num) {
        strip = num;
    }

    /**
     * Work silently unless an error occurs; optional, default=false
     */
    public void setQuiet(boolean q) {
        quiet = q;
    }

    /**
     * Assume patch was created with old and new files swapped; optional,
     * default=false
     */
    public void setReverse(boolean r) {
        reverse = r;
    }


    /**
     * Adds a FilterChain.
     */
    public FilterChain createFilterChain() {
        FilterChain filterChain = new FilterChain();
        filterChains.addElement(filterChain);
        return filterChain;
    }

    /**
     * Adds a filterset.
     */
    public FilterSet createFilterSet() {
        FilterSet filterSet = new FilterSet();
        filterSets.addElement(filterSet);
        return filterSet;
    }

    /**
     * Get the filtersets being applied to this operation.
     *
     * @return a vector of FilterSet objects
     */
    protected Vector getFilterSets() {
        return filterSets;
    }

    /**
     * Get the filterchains being applied to this operation.
     *
     * @return a vector of FilterChain objects
     */
    protected Vector getFilterChains() {
        return filterChains;
    }

    /**
     * If true, enables filtering.
     */
    public void setFiltering(boolean filtering) {
        this.filtering = filtering;
    }

    /**
     * Used to force listing of all names of copied files.
     */
    public void setVerbose(boolean verbose) {
        if (verbose) {
            this.verbosity = Project.MSG_INFO;
        } else {
            this.verbosity = Project.MSG_VERBOSE;
        }
    }

    /**
     * Used to copy empty directories.
     */
    //public void setIncludeEmptyDirs(boolean includeEmpty) {
    //    this.includeEmpty = includeEmpty;
    //}

    /**
     * If false, note errors to the output but keep going.
     * @param failonerror true or false
     */
     public void setFailOnError(boolean failonerror) {
         this.failonerror = failonerror;
     }

    /**
     * Adds a set of files to copy.
     */
    public void addFileset(FileSet set) {
        filesets.addElement(set);
    }

    /**
     * Defines the mapper to map source to destination files.
     */
    public Mapper createMapper() throws BuildException {
        if (mapperElement != null) {
            throw new BuildException("Cannot define more than one mapper",
                                     location);
        }
        mapperElement = new Mapper(project);
        return mapperElement;
    }

    /**
     * Sets the character encoding
     *
     * @since 1.32, Ant 1.5
     */
    public void setEncoding (String encoding) {
        this.encoding = encoding;
    }

    /**
     * @return the character encoding, <code>null</code> if not set.
     *
     * @since 1.32, Ant 1.5
     */
    public String getEncoding() {
        return encoding;
    }

    /**
     * Performs the copy operation.
     */
    public void execute() throws BuildException {
        File savedFile = file; // may be altered in validateAttributes
        File savedDestFile = destFile;
        File savedDestDir = destDir;
        File savedDiffDir = diffDir;
        FileSet savedFileSet = null;
        if (file == null && destFile != null && filesets.size() == 1) {
            // will be removed in validateAttributes
            savedFileSet = (FileSet) filesets.elementAt(0);
        }
        
        // make sure we don't have an illegal set of options
        validateAttributes();

        try {
            
            // deal with the single file
            if (file != null) {
                if (file.exists()) {
                    if (destFile == null) {
                        destFile = new File(destDir, file.getName());
                    }

                    if (forcediff ||
                        (file.lastModified() > destFile.lastModified())) {
                        fileCopyMap.put(file.getAbsolutePath(), 
                                        destFile.getAbsolutePath());
                    } else {
                        log(file + " omitted as " + destFile 
                            + " is up to date.", Project.MSG_VERBOSE);
                    }
                } else {
                    String message = "Warning: Could not find file "
                        + file.getAbsolutePath() + " to copy.";
                    if (!failonerror) {
                        log(message);
                    } else {
                        throw new BuildException(message);
                    }
                }
            }

            // deal with the filesets
            for (int i = 0; i < filesets.size(); i++) {
                FileSet fs = (FileSet) filesets.elementAt(i);
                DirectoryScanner ds = fs.getDirectoryScanner(project);
                File fromDir = fs.getDir(project);
                
                String[] srcFiles = ds.getIncludedFiles();
                String[] srcDirs = ds.getIncludedDirectories();
                boolean isEverythingIncluded = ds.isEverythingIncluded();
                if (isEverythingIncluded
                    && !flatten && mapperElement == null) {
                    completeDirMap.put(fromDir, destDir);
                }
                scan(fromDir, destDir, srcFiles, srcDirs);
            }
            
            // do all the copy operations now...
            doFileOperations();
        } finally {
            // clean up again, so this instance can be used a second
            // time
            file = savedFile;
            destFile = savedDestFile;
            destDir = savedDestDir;
            if (savedFileSet != null) {
                filesets.insertElementAt(savedFileSet, 0);
            }

            fileCopyMap.clear();
            dirCopyMap.clear();
            completeDirMap.clear();
        }
    }

//************************************************************************
//  protected and private methods
//************************************************************************

    /**
     * Ensure we have a consistent and legal set of attributes, and set
     * any internal flags necessary based on different combinations
     * of attributes.
     */
    protected void validateAttributes() throws BuildException {
        if (file == null && filesets.size() == 0) {
            throw new BuildException("Specify at least one source "
                                     + "- a file or a fileset.");
        }

        if (destFile != null && destDir != null) {
            throw new BuildException("Only one of tofile and todir "
                                     + "may be set.");
        }

        if (diffDir == null) {
            throw new BuildException("diffdir ouput dir must be set.");
        }

        if (!diffDir.exists()) {
            if (!diffDir.mkdirs()) {
                log("Unable to create merge output directory " 
                    + diffDir.getAbsolutePath(), Project.MSG_ERR);
                throw new BuildException("Unable to create merge output directory " 
                                         + diffDir.getAbsolutePath());
            }
        }

        if (destFile == null && destDir == null) {
            throw new BuildException("One of tofile or todir must be set.");
        }

        if (file != null && file.exists() && file.isDirectory()) {
            throw new BuildException("Use a fileset to merge directories.");
        }

        if (destFile != null && filesets.size() > 0) {
            if (filesets.size() > 1) {
                throw new BuildException(
                    "Cannot concatenate multiple files into a single file.");
            } else {
                FileSet fs = (FileSet) filesets.elementAt(0);
                DirectoryScanner ds = fs.getDirectoryScanner(project);
                String[] srcFiles = ds.getIncludedFiles();

                if (srcFiles.length == 0) {
                    throw new BuildException(
                        "Cannot perform operation from directory to file.");
                } else if (srcFiles.length == 1) {
                    if (file == null) {
                        file = new File(ds.getBasedir(), srcFiles[0]);
                        filesets.removeElementAt(0);
                    } else {
                        throw new BuildException("Cannot concatenate multiple "
                                                 + "files into a single file.");
                    }
                } else {
                    throw new BuildException("Cannot concatenate multiple "
                                             + "files into a single file.");
                }
            }
        }

        if (destFile != null) {
            destDir = fileUtils.getParentFile(destFile);
        }

    }

    /**
     * Compares source files to destination files to see if they should be
     * copied.
     */
    protected void scan(File fromDir, File toDir, String[] files, 
                        String[] dirs) {
        FileNameMapper mapper = null;
        if (mapperElement != null) {
            mapper = mapperElement.getImplementation();
        } else if (flatten) {
            mapper = new FlatFileNameMapper();
        } else {
            mapper = new IdentityMapper();
        }

        buildMap(fromDir, toDir, files, mapper, fileCopyMap);

        if (includeEmpty) {
            buildMap(fromDir, toDir, dirs, mapper, dirCopyMap);
        }
    }

    protected void buildMap(File fromDir, File toDir, String[] names,
                            FileNameMapper mapper, Hashtable map) {

        String[] toCopy = null;
        if (forcediff) {
            Vector v = new Vector();
            for (int i = 0; i < names.length; i++) {
                if (mapper.mapFileName(names[i]) != null) {
                    v.addElement(names[i]);
                }
            }
            toCopy = new String[v.size()];
            v.copyInto(toCopy);
        } else {
            SourceFileScanner ds = new SourceFileScanner(this);
            toCopy = ds.restrict(names, fromDir, toDir, mapper);
        }

        for (int i = 0; i < toCopy.length; i++) {
            File src = new File(fromDir, toCopy[i]);
            File dest = new File(toDir, mapper.mapFileName(toCopy[i])[0]);
            map.put(src.getAbsolutePath(), dest.getAbsolutePath());
        }
    }

    /**
     * Actually does the file (and possibly empty directory) merging.
     * This is a good method for subclasses to override.
     */
    protected void doFileOperations() {
        Map myLateCopy = new HashMap();
        if (fileCopyMap.size() > 0) {
            log("Merging " + fileCopyMap.size() 
                + " file" + (fileCopyMap.size() == 1 ? "" : "s") 
                + " to " + destDir.getAbsolutePath());

            Enumeration e = fileCopyMap.keys();
            while (e.hasMoreElements()) {
                String fromFile = (String) e.nextElement();
                String toFile = (String) fileCopyMap.get(fromFile);
                
                log("Merging from " + fromFile + " to " + toFile, verbosity);

                if (fromFile.equals(toFile)) {
                    log("Skipping self-copy of " + fromFile, verbosity);
                    continue;
                }

                try { 
                    File myFromFile =  new File(fromFile);
                    File myToFile =  new File(toFile);

                    if(myToFile.exists()) {
                        log("Merging " + fromFile + " to " + toFile);

                        String[] myStrings = new String[3];
                        myStrings[0] = diffType;
                        myStrings[1] = toFile;
                        myStrings[2] = fromFile;
                        
                        StringWriter myStringWriter = new StringWriter();
                        PrintWriter  myWriter       = new PrintWriter(myStringWriter);
                        DiffPrint    myDiffPrint    = new DiffPrint();
                        myDiffPrint.doWork(myStrings, myWriter);

                        myWriter.flush();
                        myWriter.close();
                        String myDiff = myStringWriter.toString();

                        if(myDiff.length() > 0) {
                            log("Merge output " + myDiff, verbosity);
                        
                            File myDiffFile = fileUtils.createTempFile("patch_" + myToFile.getName() + "_-", ".diff", diffDir);
                            
                            FileWriter myFileWriter = new FileWriter(myDiffFile);
                            myFileWriter.write(myDiff);
                            myFileWriter.flush();
                            myFileWriter.close();
                            myFileWriter = null;

                            log("Patching file " + toFile + " with diff patch " + myDiffFile.getAbsolutePath());
                            
                            Patch myPatch = new Patch();
                            myPatch.setProject(getProject());
                            myPatch.setOwningTarget(getOwningTarget());
                            myPatch.setTaskName(getTaskName());
                            myPatch.setDescription(getDescription());
                            myPatch.setLocation(getLocation());
                            myPatch.setRuntimeConfigurableWrapper(getRuntimeConfigurableWrapper());
                            
                            myPatch.setOriginalfile(new File(toFile));
                            myPatch.setPatchfile(myDiffFile);
                            myPatch.setIgnorewhitespace(ignorewhitespace);
                            if(strip >= 0) {
                                myPatch.setStrip(strip);
                            }
                            myPatch.setQuiet(quiet);
                            myPatch.setReverse(reverse);
                            myPatch.setBackups(backups);
                            myPatch.init();
                            myPatch.execute();
                            myPatch = null;
                        }
                        else {
                            log("Merge unnecessary for " + toFile, verbosity);
                        }
                    }
                    else {
                        File myNewFile = new File(toFile);
                        myLateCopy.put(myNewFile, myFromFile);
                    }

                } catch (IOException ioe) {
                    String message = "Failed to merge " + fromFile + " to " + toFile
                        + " due to " + ioe.getMessage();
                    if (!failonerror) {
                        log(message);
                    } else {
                        throw new BuildException(message);
                    }
                }
            }
        }

        if (includeEmpty) {
            Enumeration e = dirCopyMap.elements();
            int count = 0;
            while (e.hasMoreElements()) {
                File d = new File((String) e.nextElement());
                if (!d.exists()) {
                    if (!d.mkdirs()) {
                        log("Unable to create directory " 
                            + d.getAbsolutePath(), Project.MSG_ERR);
                    } else {
                        count++;
                    }
                }
            }

            if (count > 0) {
                log("Copied " + count +
                    " empty director" +
                    (count == 1 ? "y" : "ies") +
                    " to " + destDir.getAbsolutePath());
            }
        }
        if(myLateCopy.size() > 0) {
            Set myKeySet = myLateCopy.keySet();
            Iterator myKeyIterator = myKeySet.iterator();

            while(myKeyIterator.hasNext()) {
                File myNewFile  = (File) myKeyIterator.next();
                File myFromFile = (File) myLateCopy.get(myNewFile);
                try {
                    fileUtils.copyFile(myFromFile, myNewFile);
                } catch (IOException ioe) {
                    String message = "Failed to copy " + myFromFile.getName()
                        + " due to " + ioe.getMessage();
                    if (!failonerror) {
                        log(message);
                    } else {
                        throw new BuildException(message);
                    }
                }

            }
        }
    }

}

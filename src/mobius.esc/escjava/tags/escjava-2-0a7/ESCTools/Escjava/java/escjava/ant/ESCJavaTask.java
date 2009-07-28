package escjava.ant;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Project;
import org.apache.tools.ant.taskdefs.Execute;
import org.apache.tools.ant.taskdefs.Javac;
import org.apache.tools.ant.taskdefs.LogStreamHandler;
import org.apache.tools.ant.types.Commandline;
import org.apache.tools.ant.types.Path;
import org.apache.tools.ant.util.FileUtils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;


/**
 * Define an Escj compiler adapter.  This class is only a very simple wrapper
 * and does not try to implement of the command line options of escj.
 *
 * @author wsargent
 * @version $Revision$
 *
 * @since May 16, 2004
 */
public class ESCJavaTask extends DefaultCompilerAdapter
{
    private FileUtils fileUtils = FileUtils.newFileUtils();

    /* (non-Javadoc)
     * @see org.apache.tools.ant.taskdefs.compilers.DefaultCompilerAdapter#execute()
     */
    public boolean execute() throws BuildException
    {
        if (super.attributes == null)
        {
            throw new BuildException("Null attributes");
        }

        if (super.project == null)
        {
            throw new BuildException("Null project");
        }

        Javac javac = getJavac();

        if (javac == null)
        {
            throw new BuildException("null javac");
        }

        super.attributes.log("Using escj compiler", 3);

        Path classpath = new Path(super.project);

        if (super.bootclasspath != null)
        {
            classpath.append(super.bootclasspath);
        }

        classpath.addExtdirs(super.extdirs);

        if ((super.bootclasspath == null) || (super.bootclasspath.size() == 0))
        {
            super.includeJavaRuntime = true;
        }

        classpath.append(getCompileClasspath());

        if (super.compileSourcepath != null)
        {
            classpath.append(super.compileSourcepath);
        } else
        {
            classpath.append(super.src);
        }

        Commandline cmd = new Commandline();
        String exec = javac.getExecutable();
        cmd.setExecutable((exec != null) ? exec : "java");

        String simplifyProperty = super.project.getProperty(
                "build.compiler.simplify");

        // Make sure the simplify argument comes before...
        if (simplifyProperty != null)
        {
            cmd.createArgument().setValue("-Dsimplify=" + simplifyProperty);
        }

        cmd.createArgument().setValue("-classpath");
        cmd.createArgument().setPath(classpath);

        cmd.createArgument().setValue("escjava.Main");

        cmd.createArgument().setValue("-classpath");
        cmd.createArgument().setPath(classpath);

        /*
           if (super.deprecation)
           {
               cmd.createArgument().setValue("-deprecation");
           }
         */
        /*
           if (super.destDir != null)
           {
                   cmd.createArgument().setValue("-d");
                   cmd.createArgument().setFile(super.destDir);
           }
         */
        /*
           if (super.encoding != null)
           {
               cmd.createArgument().setValue("-encoding");
               cmd.createArgument().setValue(super.encoding);
           }
         */
        /*
           if (super.debug)
           {
               cmd.createArgument().setValue("-g");
           }
         */
        /*
           if (super.optimize)
           {
               cmd.createArgument().setValue("-O");
           }
         */
        setCounterExample(cmd);
        setDepend(cmd);
        setEajava(cmd);
        setEajml(cmd);
        setEnableAssertions(cmd);
        setLoopsafe(cmd);
        setLoop(cmd);
        setNoCheck(cmd);
        setNoCautions(cmd);
        setNoRedundancy(cmd);
        setNoTrace(cmd);
        setNoWarn(cmd);
        setPxLog(cmd);
        setPlainWarning(cmd);
        setQuiet(cmd);
        setRoutine(cmd);
        setRoutineIndirect(cmd);
        setSource(cmd);
        setSourcePath(cmd);
        setSuggest(cmd);
        setSxLog(cmd);
        setTarget(cmd);
        setTypeCheck(cmd);
        setUseVars(cmd);
        setUseFcns(cmd);
        setUseVarsForModelVars(cmd);
        setUseFcnsForModelVars(cmd);
        setWarn(cmd);
        setVerbose(cmd);

        // Set the -f value to use the files following.
        cmd.createArgument().setValue("-f");

        addCurrentCompilerArgs(cmd);

        int firstFileName = cmd.size();
        logAndAddFilesToCompile(cmd);

        return executeExternalCompile(cmd.getCommandline(), firstFileName) == 0;
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setUseFcnsForModelVars(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "usefcnsformodelvars", "useFcnsForModelVars");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setUseVarsForModelVars(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "usevarsformodelvars", "useVarsForModelVars");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setWarn(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "warn", "warn");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setUseFcns(Commandline cmd) throws BuildException
    {
        setArgument(cmd, "usefcns", "useFcns");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setRoutineIndirect(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "routineindirect", "routineIndirect");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setPlainWarning(Commandline cmd) throws BuildException
    {
        setArgument(cmd, "plainwarning", "plainwarning");
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setRoutine(Commandline cmd) throws BuildException
    {
        String arg = "routine";
        setTextArgument(cmd, arg, arg);
    }

    /**
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setLoop(Commandline cmd) throws BuildException
    {
        String arg = "loop";
        setTextArgument(cmd, arg, arg);
    }

    /**
     * Sets the -quiet option.
     *
     * <esc>requires cmd != null;</esc>
     *
     * @param cmd
     */
    private void setQuiet(Commandline cmd) throws BuildException
    {
        String arg = "quiet";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setVerbose(Commandline cmd)
    {
        if (super.verbose)
        {
            cmd.createArgument().setValue("-v");
        }
    }

    /*@ requires cmd != null; @*/
    private void setDepend(Commandline cmd)
    {
        if (super.depend)
        {
            cmd.createArgument().setValue("-depend");
        }
    }

    /*@ requires cmd != null; @*/
    private void setTarget(Commandline cmd)
    {
        if (super.target != null)
        {
            cmd.createArgument().setValue("-target");
            cmd.createArgument().setValue(super.target);
        }
    }

    /*@ requires cmd != null; @*/
    private void setNoWarn(Commandline cmd) throws BuildException
    {
        if (super.attributes == null)
        {
            throw new BuildException("Null attributes");
        }

        if (super.attributes.getNowarn())
        {
            cmd.createArgument().setValue("-nowarn");
        }
    }

    /*@ requires cmd != null; @*/
    private void setSource(Commandline cmd) throws BuildException
    {
        if (super.attributes == null)
        {
            throw new BuildException("Null attributes");
        }

        if (super.attributes.getSource() != null)
        {
            cmd.createArgument().setValue("-source");
            cmd.createArgument().setValue(super.attributes.getSource());
        }
    }

    /*@ requires cmd != null; @*/
    private void setSourcePath(Commandline cmd) throws BuildException
    {
        if (super.attributes == null)
        {
            throw new BuildException("Null attributes");
        }

        if (super.attributes.getSourcepath() != null)
        {
            cmd.createArgument().setValue("-sourcepath");

            Path path = super.attributes.getSourcepath();
            String pathString = (path == null) ? null : path.toString();
            cmd.createArgument().setValue(pathString);
        }
    }

    /*@ requires cmd != null; @*/
    private void setSxLog(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "sxlog", "sxLog");
    }

    /*@ requires cmd != null; @*/
    private void setPxLog(Commandline cmd) throws BuildException
    {
        setTextArgument(cmd, "pxlog", "pxLog");
    }

    /*@ requires cmd != null; @*/
    private void setCounterExample(Commandline cmd) throws BuildException
    {
        String arg = "counterexample";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setEajava(Commandline cmd) throws BuildException
    {
        String arg = "eajava";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setEajml(Commandline cmd) throws BuildException
    {
        String arg = "eajml";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setEnableAssertions(Commandline cmd) throws BuildException
    {
        String arg = "enableassertions";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setUseVars(Commandline cmd) throws BuildException
    {
        String arg = "usevars";
        setArgument(cmd, arg, "useVars");
    }

    /*@ requires cmd != null; @*/
    private void setTypeCheck(Commandline cmd) throws BuildException
    {
        String arg = "typecheck";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setSuggest(Commandline cmd) throws BuildException
    {
        String arg = "suggest";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setNoTrace(Commandline cmd) throws BuildException
    {
        String arg = "notrace";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setNoRedundancy(Commandline cmd) throws BuildException
    {
        String arg = "noredundancy";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setNoCautions(Commandline cmd) throws BuildException
    {
        String arg = "nocautions";
        setArgument(cmd, arg, "noCautions");
    }

    /*@ requires cmd != null; @*/
    private void setNoCheck(Commandline cmd) throws BuildException
    {
        String arg = "nocheck";
        setArgument(cmd, arg, arg);
    }

    /*@ requires cmd != null; @*/
    private void setLoopsafe(Commandline cmd) throws BuildException
    {
        String arg = "loopsafe";
        setArgument(cmd, arg, arg);
    }

    /**
     * Do the compile with the specified arguments.
     *
     * <esc>
     *   also requires args != null;
     * </esc>
     *
     *
     * @param args - arguments to pass to process on command line
     * @param firstFileName - index of the first source file in args, if the
     *        index is negative, no temporary file will ever be created, but
     *        this may hit the command line length limit on your system.
     * @param quoteFiles - if set to true, filenames containing spaces will be
     *        quoted when they appear in the external file. This is necessary
     *        when running JDK 1.4's javac and probably others.
     *
     * @return DOCUMENT ME!
     *
     * @throws BuildException DOCUMENT ME!
     *
     * @since Ant 1.6
     */
    protected int executeExternalCompile(String[] args, int firstFileName,
        boolean quoteFiles)
    {
        String[] commandArray = null;
        File tmpFile = null;

        try
        {
      
            /*
             * Many system have been reported to get into trouble with
             * long command lines - no, not only Windows ;-).
             *
             * POSIX seems to define a lower limit of 4k, so use a temporary
             * file if the total length of the command line exceeds this limit.
             */
            if ((Commandline.toString(args).length() > 4096) && (firstFileName >= 0))
            {
                PrintWriter out = null;

                try
                {
                    File userDir = getJavac().getTempdir();

                    if (userDir == null)
                    {
                        String userDirName = System.getProperty("user.dir");
                        userDir = new File(userDirName);
                    }

                    tmpFile = fileUtils.createTempFile("files", "", userDir);
                    tmpFile.deleteOnExit();
                    out = new PrintWriter(new FileWriter(tmpFile));

                    for (int i = firstFileName; i < args.length; i++)
                    {
                        if (quoteFiles && (args[i].indexOf(" ") > -1))
                        {
                            args[i] = args[i].replace('\\', '/');
                            out.println("\"" + args[i] + "\"");
                        } else
                        {
                            out.println(args[i]);
                        }
                    }

                    out.flush();
                    commandArray = new String[firstFileName + 1];
                    System.arraycopy(args, 0, commandArray, 0, firstFileName);
                    commandArray[firstFileName] = tmpFile.toString();
                } catch (IOException e)
                {
                    throw new BuildException("Error creating temporary file",
                        e, location);
                } finally
                {
                    if (out != null)
                    {
                        try
                        {
                            out.close();
                        } catch (Throwable t)
                        {
                            // ignore
                        }
                    }
                }
            } else
            {
                commandArray = args;
            }

            try
            {
                Execute exe = new Execute(new LogStreamHandler(attributes,
                            Project.MSG_INFO, Project.MSG_WARN));
                exe.setAntRun(project);
                exe.setWorkingDirectory(project.getBaseDir());
                exe.setCommandline(commandArray);
                exe.execute();

                return exe.getExitValue();
            } catch (IOException e)
            {
                throw new BuildException("Error running " + args[0] +
                    " compiler", e, location);
            }
        } finally
        {
            if (tmpFile != null)
            {
                tmpFile.delete();
            }
        }
    }

    /**
     * Sets an argument with a text value from a property.
     *
     * <esc>
     *   requires cmd != null;
     *   requires pPropertyName != null;
     *   requires pArgumentName != null;
     * </esc>
     *
     * @param cmd
     * @param pPropertyName
     * @param pArgumentName
     *
     * @throws BuildException if one of the arguments is null.
     */
    private void setTextArgument(Commandline cmd, String pPropertyName,
        String pArgumentName) throws BuildException
    {
        if (cmd == null)
        {
            throw new BuildException("null cmd");
        }

        if (pPropertyName == null)
        {
            throw new BuildException("null pName");
        }

        if (pArgumentName == null)
        {
            throw new BuildException("null pArgument");
        }
        
        if (super.project == null)
        {
            throw new BuildException("null project");
        }

        String propertyValue = super.project.getProperty("build.compiler." +
                pPropertyName);

        if (propertyValue != null)
        {
            cmd.createArgument().setValue("-" + pArgumentName + "=" +
                propertyValue);
        }
    }

    /**
     * Sets an argument on the commandline from a boolean property.
     *
     * <esc>
     *   requires cmd != null;
     *   requires pPropertyName != null;
     *   requires pArgumentName != null;
     * </esc>
     *
     * @param cmd
     * @param pPropertyName
     * @param pArgumentName
     *
     * @throws BuildException DOCUMENT ME!
     */
    private void setArgument(Commandline cmd, String pPropertyName,
        String pArgumentName) throws BuildException
    {
        if (cmd == null)
        {
            throw new BuildException("null cmd");
        }

        if (pPropertyName == null)
        {
            throw new BuildException("null pName");
        }

        if (pArgumentName == null)
        {
            throw new BuildException("null pArgument");
        }
        
        if (super.project == null)
        {
            throw new BuildException("null super.project");
        }

        String propertyName = super.project.getProperty("build.compiler." +
                pPropertyName);

        if ((propertyName != null) && Project.toBoolean(propertyName))
        {
            cmd.createArgument().setValue("-" + pArgumentName);
        }
    }
}
# build.compiler=jikes
# build.compiler.pedantic=true

build.compiler=org.apache.tools.ant.taskdefs.compilers.ESCJavaTask
build.compiler.quiet=true
build.compiler.simplify=c:/home/wsargent/work/esc2/Simplify-1.5.4.exe

# build.compiler.counterexample=true 
# build.compiler.disableassertions=true
# build.compiler.eajava=true
# build.compiler.eajml=true
# build.compiler.enableassertions=true
# build.compiler.loopsafe=true
# build.compiler.loop=5
# build.compiler.nocheck=true
# build.compiler.nocautions=true
# build.compiler.noredundancy=true
# build.compiler.notrace=true
# build.compiler.nowarn=category
# build.compiler.plainwarning=true
# build.compiler.pxlog=c:/home/wsargent/work/esc2/pxlog.log
# build.compiler.quiet=true
# build.compiler.routine=1414
# build.compiler.routineindirect=5
# build.compiler.suggest=true
# build.compiler.sxlog=c:/home/wsargent/work/esc2/sxlog.log
# build.compiler.typecheck=true
# build.compiler.usevars=true
# build.compiler.usefunctions=true
# build.compiler.usefcns=true
# build.compiler.warn=category

package org.apache.tools.ant.types;

import java.io.File;
import java.util.StringTokenizer;
import java.util.Vector;
import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;
import java.util.LinkedList;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.ProjectComponent;
import org.apache.tools.ant.util.StringUtils;


/**
 * Commandline objects help handling command lines specifying processes to
 * execute.
 *
 * The class can be used to define a command line as nested elements or as a
 * helper to define a command line by an application.
 * <p>
 * <code>
 * &lt;someelement&gt;<br>
 * &nbsp;&nbsp;&lt;acommandline executable="/executable/to/run"&gt;<br>
 * &nbsp;&nbsp;&nbsp;&nbsp;&lt;argument value="argument 1" /&gt;<br>
 * &nbsp;&nbsp;&nbsp;&nbsp;&lt;argument line="argument_1 argument_2 argument_3" /&gt;<br>
 * &nbsp;&nbsp;&nbsp;&nbsp;&lt;argument value="argument 4" /&gt;<br>
 * &nbsp;&nbsp;&lt;/acommandline&gt;<br>
 * &lt;/someelement&gt;<br>
 * </code>
 * The element <code>someelement</code> must provide a method
 * <code>createAcommandline</code> which returns an instance of this class.
 *
 * @author thomas.haas@softwired-inc.com
 * @author Stefan Bodewig
 */
public class Commandline implements Cloneable {


    /*@  public normal_behavior
      @   requires toProcess != null;
      @*/
    public /*@ pure @*/ Commandline(String toProcess);

    /*@ public normal_behavior
      @     
      @*/
    public /*@ pure @*/ Commandline();

	/*@  public normal_behavior
      @    ensures \result != null;
      @*/
    public /*@ pure @*/ Argument createArgument();
    
	/*@  public normal_behavior
      @    ensures \result != null;
      @*/
    public static String toString(String [] line);

}

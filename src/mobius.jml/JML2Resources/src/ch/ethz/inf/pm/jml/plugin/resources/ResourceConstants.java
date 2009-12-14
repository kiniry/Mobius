/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2003-2008 Swiss Federal Institute of Technology Zurich
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Paolo Bazzi, Summer 2006
 *
 */

package ch.ethz.inf.pm.jml.plugin.resources;

/**
 * @author Paolo Bazzi
 *
 */
public class ResourceConstants {

	/** The name of the library needed to run JML Tools. */
    static final public String JML_RELEASE_LIBRARY_NAME = "jml-release.jar";

    /** The name of the library needed to run JML Rac Tools. */
    // static final public String JML_RUNTIME_LIBRARY_NAME = "jmlruntime.jar";

    /** The name of the jml-specs library needed to run JML Tools. */
    static final public String JML_SPECS_PATH_NAME = "specs";

    /** The name of the JML Resources Plugin */
    static final public String JML_RESOURCES_PLUGIN_NAME = "ch.ethz.inf.pm.jml.plugin.resources";

    public static final String PLUGIN_DEF_PROPERTIES_FILE = "jmlplugin.default.properties";
    public static final String CHECKER_DEF_PROPERTIES_FILE = "jmlchecker.default.properties";
	public static final String COMPILER_DEF_PROPERTIES_FILE = "jmlcompiler.default.properties";
	public static final String RAC_DEF_PROPERTIES_FILE = "jmlrac.default.properties";

    public static final String PATH_SEPARATOR = System.getProperty("path.separator");
    public static final String FILE_SEPARATOR = System.getProperty("file.separator");

	public static final String DEFAULT_OUT = "jml-compiled/";
}

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

package ch.ethz.inf.pm.jml.plugin.internal.core;

import java.io.ByteArrayOutputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.jmlspecs.checker.JmlCommonOptions;
import org.jmlspecs.jmlrac.RacOptions;

import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlCompilerProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;


/**
 * @author Paolo Bazzi
 * @author WMD
 */
public class JmlCompilerRunner extends JmlCheckerRunner {
	@Override
	protected String getRunnerName() {
		return "JML2 compiler";
	}

	@Override
	protected RacOptions createOptions(IFile file) throws CoreException {
		RacOptions racOpt = new RacOptions();
		IProject proj = file.getProject();

		setCheckerProperties(racOpt, proj);
		setCompilerProperties(racOpt, proj);

		return racOpt;
	}


	@Override
	protected boolean  exec(String[] arg, JmlCommonOptions jmlComOpt, ByteArrayOutputStream baos) {
		RacOptions racOpt = (RacOptions) jmlComOpt;
		return org.jmlspecs.jmlrac.Main.compile(arg, racOpt, baos);
	}


	protected void setCompilerProperties(RacOptions racOpt, IProject proj)
	throws CoreException {
		JmlPropertiesProvider compilerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.COMPILER_DEF_PROPERTIES_FILE);

		racOpt.set_neutralContext(compilerProps.getBooleanProperty(JmlCompilerProperties.NEUTRAL_CONTEXT,proj));
		racOpt.set_noSource(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_SOURCE,proj));
		racOpt.set_noredundancy(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_REDUNDANCY,proj));
		racOpt.set_noreflection(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_REFLECTION,proj));
		racOpt.set_nowrite(compilerProps.getBooleanProperty(JmlCompilerProperties.NO_WRITE,proj));
		String packageName = compilerProps.getProperty(JmlCompilerProperties.PACKAGE_NAME,proj);
		if (packageName != null && !packageName.equalsIgnoreCase("")) { racOpt.set_packageName(packageName); }
		String filter = compilerProps.getProperty(JmlCompilerProperties.FILTER,proj);
		if (filter != null && !filter.equalsIgnoreCase("")) { racOpt.set_filter(filter); }
		racOpt.set_print(compilerProps.getBooleanProperty(JmlCompilerProperties.PRINT,proj));
		racOpt.set_recursiveType(compilerProps.getBooleanProperty(JmlCompilerProperties.RECURSIVE_TYPE,proj));
		racOpt.set_oldSemantics(compilerProps.getBooleanProperty(JmlCompilerProperties.OLD_SEMANTICS,proj));
		racOpt.set_mustBeExecutable(compilerProps.getBooleanProperty(JmlCompilerProperties.MUST_BE_EXECUTABLE,proj));
	}
}

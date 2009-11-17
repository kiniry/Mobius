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
import org.jmlspecs.jmlexec.ExecOptions;


/**
 * @author WMD
 */
public class JmlExecRunner extends JmlCompilerRunner {
	@Override
	protected String getRunnerName() {
		return "JML2 exec";
	}

	@Override
	protected ExecOptions createOptions(IFile file) throws CoreException {
		ExecOptions exeOpt = new ExecOptions();
		IProject proj = file.getProject();

		setCheckerProperties(exeOpt, proj);
		setCompilerProperties(exeOpt, proj);

		return exeOpt;
	}

	@Override
	protected boolean  exec(String[] arg, JmlCommonOptions jmlComOpt, ByteArrayOutputStream baos) {
		ExecOptions exeOpt = (ExecOptions) jmlComOpt;
		return org.jmlspecs.jmlexec.Main.compile(arg, exeOpt, baos);
	}
}

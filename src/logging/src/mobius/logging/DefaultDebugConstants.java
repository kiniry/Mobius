/*
 * Software Engineering Tools.
 *
 * $Id: DefaultDebugConstants.jass,v 1.1.1.1 2002/12/29 12:36:14 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * 
 * - Neither the name of the Joseph Kiniry, KindSoftware, nor the
 * California Institute of Technology, nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 * IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL KIND SOFTWARE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package mobius.logging;

import java.util.Map;

/**
 * <p> The default implementation of debug semantics for the IDebug
 * framework. </p>
 *
 * @version $Revision: 1.1.1.1 $ $Date: 2002/12/29 12:36:14 $
 * @author Joseph R. Kiniry <kiniry@acm.org>
 */

public class DefaultDebugConstants implements DebugConstants
{
  // Attributes
  // Inherited Methods
  // Constructors
  // Public Methods

  /**
   * Initializes default categories of debugging facilities.
   *
   * @concurrency CONCURRENT
   * @param the_categories_map is the map to initialize.
   *
   * @see DebugConstants The default debug categories are documented in
   * DebugConstants.
   */
  //@ ensures the_categories_map.size() == 6;
  public void initCategories(/*@ non_null @*/ Map the_categories_map)
  {
    the_categories_map.put(ASSERTION, Integer.valueOf(ASSERTION_LEVEL));
    the_categories_map.put(FAILURE, Integer.valueOf(FAILURE_LEVEL));
    the_categories_map.put(CRITICAL, Integer.valueOf(CRITICAL_LEVEL));
    the_categories_map.put(ERROR, Integer.valueOf(ERROR_LEVEL));
    the_categories_map.put(WARNING, Integer.valueOf(WARNING_LEVEL));
    the_categories_map.put(NOTICE, Integer.valueOf(NOTICE_LEVEL));
  }

  /**
   * @param the_level the level to check.
   * @return a boolean indicating if the passed level is valid.
   */

  public boolean checkLevel(int the_level)
  {
    return ((LEVEL_MIN <= the_level) && (the_level <= LEVEL_MAX));
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class DefaultDebugConstants

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */


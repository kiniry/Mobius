<#include "macros.ftl"/>

<#macro ifspecreturn f><#if f.hasType??><@ptype type=f.hasType.type/><#else>Void</#if></#macro>
<#macro ifspecsig f name><a href="#<@methodlink f=f name=name/>">${name}</a><#if (f.arguments?size > 0)>(<#list f.arguments as arg><@parg arg=arg/><#if arg_has_next>, </#if></#list>)</#if></#macro>

<#macro ifspecsignoparamnames f name>${name}<#if (f.arguments?size > 0)>(<#list f.arguments as arg>${arg.type.identifier}<#if arg_has_next>,</#if></#list>)</#if></#macro>

<#macro parg arg><@ptype type=arg.type/><#if arg.identifier??> ${arg.identifier}</#if></#macro>

<h2>${qualifiedclass}</h2>

<h3>Description</h3>
<p>${class.comment!"No description"}
 <#if (class.classInterface.indexing)??>
  <@indexing indexing=class.classInterface.indexing/>
 </#if>
</p>



<#if class.classInterface??><#assign ci=class.classInterface/></#if>
<#if (ci?? && ci.parents?size > 0)>
<h3>Parents</h3>
<p><#list ci.parents as parent><@ptype type=parent/><#if parent_has_next>, </#if></#list></p>
</#if>
<#if (children?size > 0)>
<h3>Children</h3>
<p><#list children as child><@pclass class=child/><#if child_has_next>, </#if></#list></p>
</#if>
<#if (features?? && features?size > 0)>
<h3>Features</h3>
<#list features as feature>
 <#list feature.featureNames as fname>
 <#assign name=fname.name/>
  <hr/>
  <p id="<@methodlink f=feature name=name/>">
   <span class="methodsig"><@ifspecreturn f=feature/> <@ifspecsig f=feature name=name/></span>
   <#if feature.comment??>
    <br/>
    ${feature.comment}
   </#if>
   <#if (feature.contracts.preconditions?size > 0 || feature.contracts.postconditions?size > 0)>
    <br/>
    <div class="invisible specsdiv" id="${name}-spectoggle">
     <#if (feature.contracts.preconditions?size > 0)>
      Requires:<br/>
      <#list feature.contracts.preconditions as pre>
       <img src="${STUtil.getFeatureSignature(name, feature, st)}-precondition${(pre_index+1)}.png"/>
       <br/>
      </#list>
     </#if>
     <#if (feature.contracts.postconditions?size > 0)>
      Ensures:<br/>
      <#list feature.contracts.postconditions as post>
       <img src="${STUtil.getFeatureSignature(name, feature, st)}-postcondition${(post_index+1)}.png"/>
       <br/>
      </#list>
     </#if>
    </div>
   </#if>
   <#assign sourcelines=AstUtil.getSourceLines(feature)/>
   <#if (sourcelines?size > 0)>
    <div class="invisible sourcediv" id="${name}-sourcetoggle">
     <pre  class="brush: bon; toolbar: false; first-line: ${feature.getLocation().getLineNumber()};">
<#list sourcelines as line>      ${line}
      </#list>
     </pre>
    </div>
   </#if>
   <#if (feature.contracts.preconditions?size > 0 || feature.contracts.postconditions?size > 0)>
   <a href="" class="showspecslink" onclick="return toggleShow('#${name}-spectoggle',this,'Show specs','Hide specs');">Show specs</a>
   </#if>
   <#if (sourcelines?size > 0)>
   <a href="" class="showsourcelink" onclick="return toggleShow('#${name}-sourcetoggle',this,'Show source','Hide source');">Show source</a>
   </#if>
  </p>
 </#list>
</#list>
<hr/>
<#if (ci?? && ci.invariant?size > 0)>
<div class="invisible specsdiv">
 <p>
  <h3>Invariant<#if (ci.invariant?size > 1)>s</#if></h3>
  <#list ci.invariant as inv>
  <img src="${class.name.name}-invariant${(inv_index+1)}.png"/>
  <br/>
  </#list>
 </p>
 <#assign sourcelines=AstUtil.getSourceLines(ci.invariant)/>
 <#if (sourcelines?size > 0)>
  <div class="invisible sourcediv" id="${class.name.name}-invariant-sourcetoggle">
   <pre  class="brush: bon; toolbar: false; first-line: ${ci.invariant?first.getLocation().getLineNumber()};">
<#list sourcelines as line>    ${line}
    </#list>
   </pre>
  </div>
 </#if>
</div>
</#if>
<p>
 <a id="showallspecslink" href="#" onclick="return toggleShowAll('#showallspecslink','.showspecslink','.specsdiv','Show specs','Hide specs','Show all specs','Hide all specs');">Show all specs</a>
 <a id="showallsourcelink" href="#" onclick="return toggleShowAll('#showallsourcelink','.showsourcelink','.sourcediv','Show source','Hide source','Show all source','Hide all source');">Show all source</a>
</p>
</#if>
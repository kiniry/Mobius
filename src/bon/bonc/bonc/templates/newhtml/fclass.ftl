<#include "macros.ftl">
<h2>${qualifiedclass}</h2>

<h3>Description</h3>
<p>${class.comment!"No description"}</p>

<#if class.classInterface??>
<#assign ci=class.classInterface/>
<h3>Parents:</h3>
<p><#list ci.parents as parent><@type type=parent/><#if parent_has_next>, </#if></#list>
<#else>
<p> No interface!</p>
</#if>
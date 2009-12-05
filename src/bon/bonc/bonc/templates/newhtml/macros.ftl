<#macro html_header_no_close title><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-type" content="text/html; charset=iso-8859-1" />
<title>${title}</title>
</#macro>
<#macro html_header title>
<@html_header_no_close title=title/>
</head>
</#macro>

<#macro ptype type><a href="" onclick="return navTo('class:${type.identifier}:doc');">${type.identifier}</a><#if (type.actualGenerics?size > 0)>[<#list type.actualGenerics as gen><@ptype type=gen/><#if gen_has_next>,</#if></#list>]</#if></#macro>

<#macro ptypebasicstring type>${type.identifier}</a><#if (type.actualGenerics?size > 0)>[<#list type.actualGenerics as gen><@ptype type=gen/><#if gen_has_next>,</#if></#list>]</#if></#macro>

<#macro pclass class><a href="" onclick="return navTo('class:${class.name.name}');">${StringUtil.prettyPrintShortenedClass(class)}</a></#macro>

<#macro methodlink f name>class:${class.name.name}:doc:${name}</#macro>

<#macro image file>
<#assign dim=FileUtil.getImageDimensions(outputDirPath + file)/>
<#if (dim.x == -1 || dim.y == -1)>
<img src="${file}"/>
<#else>
<img src="${file}" height="${dim.y}" width="${dim.x}"/>
</#if>
</#macro>

<#macro indexing indexing>
 <dl class="indexing">
  <dt>Indexing</dt>
  <#list indexing.indexes as indexitem>
   <dd><strong>${indexitem.id}</strong> : <#list indexitem.indexTerms as term>${term}<#if term_has_next>, </#if></#list>;</dd>
  </#list>
 </dl>
</#macro>
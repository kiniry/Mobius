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

<#macro ptype type><a href="" onclick="return navTo('class:${type.identifier}');">${type.identifier}</a><#if (type.actualGenerics?size > 0)>[<#list type.actualGenerics as gen><@ptype type=gen/><#if gen_has_next>,</#if></#list>]</#if></#macro>

<#macro ptypebasicstring type>${type.identifier}</a><#if (type.actualGenerics?size > 0)>[<#list type.actualGenerics as gen><@ptype type=gen/><#if gen_has_next>,</#if></#list>]</#if></#macro>

<#macro pclass class><a href="" onclick="return navTo('class:${class.name.name}');">${StringUtil.prettyPrintShortenedClass(class)}</a></#macro>

<#macro fspec f><#list f.featureNames as name><@ifspec f=f name=name/></#list></#macro>

<#macro ifspec f name><p id="<@methodlink f=f name=name/>"><@ifspecreturn f=f/> <@ifspecsig f=f name=name/></p></#macro>

<#macro ifspecreturn f><#if f.hasType??><@ptype type=f.hasType.type/><#else>Void</#if></#macro>
<#macro ifspecsig f name><a href="<@methodlink f=f name=name/>">${name.name}</a><#if (f.arguments?size > 0)>(<#list f.arguments as arg><@parg arg=arg/><#if arg_has_next>, </#if></#list>)</#if></#macro>

<#macro ifspecsignoparamnames f name>${name.name}<#if (f.arguments?size > 0)>(<#list f.arguments as arg>${arg.type.identifier}<#if arg_has_next>,</#if></#list>)</#if></#macro>

<#macro parg arg><@ptype type=arg.type/><#if arg.identifier??> ${arg.identifier}</#if></#macro>

<#macro methodlink f name>#class:${STUtil.getQualifiedClassString(class.name.name,st)}:<@ifspecsignoparamnames f=f name=name/></#macro>
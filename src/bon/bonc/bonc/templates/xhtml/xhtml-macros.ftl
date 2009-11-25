<#macro cluster_chart_link cluster><a href="#cluster_chart:${cluster.name}" onclick="return linkSelect('cluster_chart','cluster_chart:${cluster.name}');">${cluster.name}</a></#macro>
<#macro cluster_chart_link_string cluster_name><a href="#cluster_chart:${cluster_name}" onclick="return linkSelect('cluster_chart','cluster_chart:${cluster_name}');">${cluster_name}</a></#macro>

<#macro class_chart_link clazz><a href="#class_chart:${clazz.name}" onclick="return linkSelect('class_chart','class_chart:${clazz.name}');">${clazz.name}</a></#macro>
<#macro class_chart_link_string class_name><a href="#class_chart:${class_name}" onclick="return linkSelect('class_chart','class_chart:${class_name}');">${class_name}</a></#macro>

<#macro indexingm indexing><#list indexing.indexes as indexitem>          <dd>${indexitem.id} : <#list indexitem.indexTerms as term>${term}<#if term_has_next>, </#if></#list>;</dd>
</#list></#macro>

<#macro class_or_cluster_link name><#if isCluster(name)>(<@cluster_chart_link_string cluster_name=name/>)<#else><@class_chart_link_string class_name=name/></#if></#macro>

<#include "xhtml-macros.ftl">
<#escape x as prepareManifest(x)?html>
<div class="top-level" id="cluster_chart:${name}">
  <table class="outer">
    <tr class="top">
      <th class="type">CLUSTER</th>
      <td class="name" colspan="2">${name}</td>
      <td class="part"><strong>Part:</strong> ${part!"1/1"}</td>
    </tr>
    <tr class="middle">
      <td class="explanation" colspan="2">
        <dl>
          <dt>Purpose</dt>
          <dd>${explanation!""}</dd>
        </dl>
      </td>
      <td class="indexing" colspan="2">
        <dl>
          <dt>Indexing</dt>
          <#if indexing??><@indexingm indexing=indexing/></#if>
        </dl>
      </td>
    </tr>
    <tr>
      <td colspan="4" class="bottom">
        <#if (classes?size > 0)><table>
          <tr>
            <th class="grey">Class</th>
            <th class="grey">Description</th>
          </tr>
<#list classes as clazz>          <tr>
            <td class="light-grey"><@class_chart_link clazz=clazz/></td>
            <td class="white">${clazz.description}</td>
          </tr></#list>
        </table>
        </#if><#if (clusters?size > 0)><table>
          <tr>
            <th>Cluster</th>
            <th>Description</th>
          </tr>
<#list clusters as cluster>          <tr>
            <td class="light-grey"><@cluster_chart_link cluster=cluster/></td>
            <td class="white">${cluster.description}</td>
          </tr></#list>
        </table>
        </#if>
      </td>
    </tr>
  </table>
</div>

</#escape>
<#include "xhtml-macros.ftl">
<#escape x as prepareManifest(x)?html>
<div class="top-level" id="system_chart:${name}">
  <table class="outer">
    <tr class="top">
      <th class="type">SYSTEM</th>
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
        <table>
          <tr>
            <th class="grey">Cluster</th>
            <th class="grey">Description</th>
          </tr>
<#list clusters as cluster>          <tr>
            <td class="light-grey"><@cluster_chart_link cluster=cluster/></td>
            <td class="white">${cluster.description}</td>
          </tr></#list>
        </table>
      </td>
    </tr>
  </table>
</div>

</#escape>
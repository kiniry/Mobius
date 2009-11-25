<#include "xhtml-macros.ftl">
<#escape x as prepareManifest(x)?html>
<div class="top-level" id="event_chart:${id}">
  <table class="outer">
    <tr class="top">
      <th class="type">EVENT</th>
      <td class="name" colspan="2">${systemName}</td>
      <td class="part"><strong>Part:</strong> ${part!"1/1"}</td>
    </tr>
    <tr class="middle">
      <td class="explanation" colspan="2">
        <dl>
          <dt>Comment</dt>
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
            <th class="grey"><#if incoming>incoming</#if><#if outgoing>outgoing</#if></th>
            <th class="grey">Involved object types</th>
          </tr>
<#list entries as entry>          <tr>
            <td class="light-grey">${entry.description}</td>
            <td class="white spaced-lines"><#list entry.involved as involved><@class_or_cluster_link name=involved/><#if involved_has_next>, </#if></#list></td>
          </tr></#list>
        </table>
      </td>
    </tr>
  </table>
</div>

</#escape>
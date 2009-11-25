<#include "xhtml-macros.ftl">
<#escape x as prepareManifest(x)?html>
<div class="top-level" id="class_chart:${name.name}">
  <table class="outer">
    <tr class="top">
      <th class="type">CLASS</th>
      <td class="name" colspan="2">${name.name}</td>
      <td class="part"><strong>Part:</strong> ${part!"1/1"}</td>
    </tr>
    <tr class="middle">
      <td class="explanation" colspan="2">
        <dl>
          <dt>Type Of Object</dt>
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
          <#if (inherits?size > 0)><tr>
            <th class="light-grey">Inherits from</th>
            <td class="white spaced-lines"><#list inherits as parent>${parent.name}<#if parent_has_next>, </#if></#list></td>
          </tr></#if>
          <tr>
            <th class="light-grey">Queries</th>
            <td class="white spaced-lines"><#list queries as query>${query}<#if query_has_next>,<br/></#if></#list></td>
          </tr>
          <tr>
            <th class="light-grey">Commands</th>
            <td class="white spaced-lines"><#list commands as command>${command}<#if command_has_next>,<br/></#if></#list></td>
          </tr>
          <tr>
            <th class="light-grey">Constraints</th>
            <td class="white spaced-lines"><#list constraints as constraint>${constraint}<#if constraint_has_next>,<br/></#if></#list></td>
          </tr>
        </table>
      </td>
    </tr>
  </table>
</div>

</#escape>
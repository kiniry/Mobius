<#include "macros.ftl">
<@html_header_no_close title="BON Documentation v2.0"/>
<link rel="stylesheet" type="text/css" href="style.css">

<script type="text/javascript" src="js/scripty/prototype.js"></script>
<script type="text/javascript" src="js/scripty/scriptaculous.js"></script>
<script type="text/javascript" src="js/jquery/jquery-1.3.2.js"></script>
<script type="text/javascript" src="js/jquery/jquery.history.js"></script>
<script type="text/javascript" src="js/jquery/jquery.hotkeys.js"></script>
<script type="text/javascript" src="js/vars.js"></script>
<script type="text/javascript" src="js/jdoc.js"></script>
<script type="text/javascript">
  // <![CDATA[
  var $j = jQuery.noConflict();
  $j(document).ready(setup);
  // ]]>
</script>
</head>
<body>

<div id="left-pane">
 <div id="side-bar">
  <h3>Related:</h3>
  <p id="related"></p>
  <h3>Recent:</h3>
  <p id="recent"></p>
  <h3>Most used:</h3>
  <p id="most-used"></p>
 </div>
</div>

<div id="search-pane">
  <form id="search" method="post" action="/">
   <p><input type="text" id="search-box" name="search-box" size="20"/></p>
  </form>
  <div id="search-results"></div>
</div>

<div id="right-pane">
 <div id="main-display">
 </div>
</div>

</body>
</html>

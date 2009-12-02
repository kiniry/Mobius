

function setup() {
	$j('#search-box').val('Search...');

	var initialHash = $j.history.getCurrent();
	if (!processHash(initialHash)) {
		$j('#main-display').load('all-classes.html');
	}
	$j(document).history(function(e,curr,prev) { processHash(curr); });

	var autocompleter = new Autocompleter.Local('search-box', 'search-results', elements_list, {updateElement: selectedAuto, partialChars: 1, fullSearch: true});

	$j('#search-box').focus(function(event){
		$('search-box').morph('width: 500px; font-size: 20px;', {duration: 0.2});
		$('search-pane').morph('width: 500px; font-size: 20px;', {duration: 0.2});
		$('main-display').morph('opacity: 0.1', {duration: 0.2});
		$('side-bar').morph('opacity: 0.3', {duration: 0.2});
		if ($j('#search-box').val() == 'Search...') {
			$j('#search-box').val('');
		} else if ($j('#search-box').val() != '') {
			setTimeout(function(){ autocompleter.show(); }, 250);
		}
	});

	//On search box lose focus, restore search box (and  small size
	$j('#search-box').blur(function(event){
		$('search-box').morph('width: 150px; font-size: 12px;', {duration: 0.2});
		$('search-pane').morph('width: 200px; font-size: 20px;', {duration: 0.2});
		$('main-display').morph('opacity: 1', {duration: 0.2});
		$('side-bar').morph('opacity: 1', {duration: 0.2});
		if ($j('#search-box').val() == '') {
			$j('#search-box').val('Search...');
		}
	});

	$j(document).bind('keydown', {combi: '/', disableInInput: true}, function() {
		$j('#search-box').focus();
		return false;
	});

	$j(document).bind('keydown', 'esc', function() {
		$j('#search-box').blur();
	});

	$j(document).bind('keydown', 's', function() {
		$j('#showallspecslink').click();
	});

	$j(document).bind('keydown', 'c', function() {
		$j('#showallsourcelink').click();
	});
	
	$j(document).bind('keydown', 'd', function() {
		switchToType('diagram');
	});
	
	$j(document).bind('keydown', 'f', function() {
		switchToType('doc');
	});

};

function switchToType(type) {
	var currentHash = $j.history.getCurrent();
	var parts = currentHash.split(':');
	if (parts.length >= 2) {
	  	var name = parts[1];
	  	if (parts.length < 3 || parts[2] != type) {
	  		userLoad(parts[0], name, type);
	  	}
	}
}

function selectedAuto(selectedElement) {
	var value = Element.collectTextNodesIgnoreClass(selectedElement, 'informal');
	userLoad('class', value, 'doc');
	$j('#search-box').blur(); 
}

function processHash(hash) {
	var parts = hash.split(':');
	if (parts.length >= 2) {
		parts.length >= 3 ? loadEntity(parts[0],parts[1],parts[2]) : loadEntity(parts[0],parts[1],'doc');
		return true;
	}
	return false;
}

function userLoad(entity, name, type) {
	$j.history.add(entity + ':' + name + ":" + type);
	loadEntity(entity, name, type);
}

function loadEntity(enityt, name, type) {
	var page = type == 'diagram' ? name + "-diagram.html" : name + '.html';
	$j('#main-display').load(page, function() {
		SyntaxHighlighter.highlight();  
	});
	$j('#related').load(name + '-related.html');
}

function navTo(loc) {
	var parts = loc.split(':');
	if (parts.length >= 2) {
		if (parts.length >= 3) {
			userLoad(parts[0], parts[1], parts[2]);
		} else {	
			userLoad(parts[0], parts[1], 'doc');
		}
	}
	return false;
}

function toggleShow(id,link,showtext,hidetext) {
	$j(id).toggleClass('invisible')
	if ($j(id).hasClass('invisible')) {
		$j(link).text(showtext);
	} else {
		$j(link).text(hidetext);
	}
	return false;
}

function toggleShowAll(alllinkid,singlelinkclass,showclass,showtext,hidetext,showalltext,hidealltext) {
	if ($j(alllinkid).text() == showalltext) {
		//Show all
		$j(alllinkid).text(hidealltext);
		$j(singlelinkclass).text(hidetext);
		$j(showclass).removeClass('invisible');
	} else {
		//Hide all
		$j(alllinkid).text(showalltext);
		$j(singlelinkclass).text(showtext);
		$j(showclass).addClass('invisible');
	}
	return false;
}
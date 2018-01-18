#!/usr/bin/env node
var fs = require('fs');
if (process.argv.length !== 4) {
	console.info('Usage: node extract.js input.txt output.txt');
	process.exit();
}
console.info('Reading file...');
var draft = fs.readFileSync(
	process.argv[2]
).toString();
console.log('Scanning...');
var regex = /((\w|\-)+ )?(enum|struct) {(\w|\s|\,|\/|\*|\[|\]|\<|\>|\(|\)|\.|\;|\_|\-|\^|\{|\}|\:|\=|\"|\')*?} (\[|\]|\w)+;(\s*\} (\[|\]|\w)+;)*/g;
var m = draft.match(regex);
fs.writeFileSync(process.argv[3], '');
if (m.length) {
	m.forEach(function(v, i) {
		fs.appendFileSync(process.argv[3], `${v}\n\n`);
	});
	console.info(`Results written to ${process.argv[3]}.`);
}
else {
	console.info('No matches found.');
}

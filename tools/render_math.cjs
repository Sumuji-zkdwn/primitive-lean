const fs = require('fs');
const katex = require('../vendor/katex/katex.js');
const expressions = JSON.parse(fs.readFileSync(0, 'utf8'));
process.stdout.write(JSON.stringify(expressions.map(({tex,display}) => katex.renderToString(tex, {
  displayMode:display,throwOnError:true,trust:false,strict:'error',output:'htmlAndMathml'
}))));

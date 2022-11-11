const fs = require('fs');

fs.readFile('./test.txt', function (err, data) {
    if (err) return console.error(err);
    console.log(data.toString());
})

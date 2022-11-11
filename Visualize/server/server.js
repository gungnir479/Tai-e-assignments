const http = require('http');
const dt = require('./date');

http.createServer(function (req, res){
    res.writeHead(200, {'Content-Type': 'text/html'});
    res.end('The date and time are currently: '+dt.myDateTime());
}).listen(8000);

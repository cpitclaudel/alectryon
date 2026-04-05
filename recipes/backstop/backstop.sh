#!/usr/bin/env sh
python3 -m http.server --bind 127.0.0.1 --directory ../../ 1535 &

SERVER_PID=$!
trap 'kill $SERVER_PID' EXIT

curl -sf --retry 5 --retry-connrefused --retry-delay 1 -o /dev/null http://127.0.0.1:1535/

./node_modules/.bin/backstop --config=backstop.config.js "$@"

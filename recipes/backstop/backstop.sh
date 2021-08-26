#!/usr/bin/env sh
python3 -m http.server --bind 127.0.0.1 --directory ../../ 1535 &

SERVER_PID=$!
trap 'kill $SERVER_PID' EXIT

./node_modules/.bin/backstop --config=backstop.config.js "$@"

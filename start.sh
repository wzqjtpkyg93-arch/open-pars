#!/bin/bash
set -e

config=/etc/secrets/xray.json
/usr/local/bin/xray run -test -c "$config"
/usr/local/bin/xray run -c "$config" &
xray_pid=$!

for attempt in {1..30}; do
  if ! kill -0 "$xray_pid" 2>/dev/null; then
    echo "Xray stopped during startup" >&2
    exit 1
  fi
  if ( : > /dev/tcp/127.0.0.1/1080 ) 2>/dev/null; then
    export OPENSOOQ_PROXY_URL=http://127.0.0.1:1080
    exec python -u /app/bot.py
  fi
  sleep 1
done

echo "Xray did not open port 1080" >&2
exit 1
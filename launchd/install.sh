#!/bin/sh
# Install and start the autopilot as a launchd agent for this user (runs while you are logged in).
set -e
solver=$(cd "$(dirname "$0")/.." && pwd)
dst="$HOME/Library/LaunchAgents/local.pnp-autopilot.plist"
mkdir -p "$HOME/Library/LaunchAgents" "$solver/out"
sed "s|@SOLVER@|$solver|g" "$solver/launchd/local.pnp-autopilot.plist" > "$dst"
plutil -lint "$dst"
launchctl bootout "gui/$(id -u)/local.pnp-autopilot" 2>/dev/null || true
launchctl bootstrap "gui/$(id -u)" "$dst"
echo "installed: $dst"
launchctl print "gui/$(id -u)/local.pnp-autopilot" | grep -E '^\s*(state|pid|last exit code) ='

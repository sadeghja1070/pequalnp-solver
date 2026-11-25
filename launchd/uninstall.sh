#!/bin/sh
# Stop the autopilot agent and remove it. The autopilot hands back any held step at its next start;
# to tidy now, run it once by hand: python3 -I autopilot.py --max-hours 0
launchctl bootout "gui/$(id -u)/local.pnp-autopilot" 2>/dev/null && echo "stopped" || echo "was not running"
rm -f "$HOME/Library/LaunchAgents/local.pnp-autopilot.plist" && echo "removed the agent"

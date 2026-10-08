#!/usr/bin/env bash
# Format lab diagnostics while retaining Lean's exit status.
set -uo pipefail

red=''
green=''
reset=''
if [[ -t 1 && ${TERM:-dumb} != dumb && -z ${NO_COLOR+x} ]]; then
  red=$'\033[31m'
  green=$'\033[32m'
  reset=$'\033[0m'
fi

printf '→ Checking %s\n' "$1"
lake env lean "$1" 2>&1 | awk -v red="$red" -v reset="$reset" '
  /(^|: )error:/ { printf "%sFAIL  %s%s\n", red, $0, reset; fflush(); next }
  { print; fflush() }
'
statuses=("${PIPESTATUS[@]}")
status=${statuses[0]}
if (( status == 0 )); then
  status=${statuses[1]}
fi

if (( status == 0 )); then
  printf '%sPASS — skeleton complete!%s\n' "$green" "$reset"
else
  printf '%sFAIL — fix the errors above and rerun the lab.%s\n' "$red" "$reset"
fi
exit "$status"

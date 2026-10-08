#!/usr/bin/env bash
# Report both exercise sets; required proofs determine the lab's exit status.
set -uo pipefail

red=''
green=''
yellow=''
reset=''
if [[ -t 1 && ${TERM:-dumb} != dumb && -z ${NO_COLOR+x} ]]; then
  red=$'\033[31m'
  green=$'\033[32m'
  yellow=$'\033[33m'
  reset=$'\033[0m'
fi

check_exercises() {
  local file=$1 mode=$2 status
  local -a statuses
  printf '→ Checking %s exercises: %s\n' "$mode" "$file"
  lake env lean "$file" 2>&1 | awk \
    -v mode="$mode" -v red="$red" -v yellow="$yellow" -v reset="$reset" '
    mode == "optional" && /error: declaration uses `sorry`/ {
      printf "%sOPTIONAL — PENDING  %s%s\n", yellow, $0, reset; fflush(); next
    }
    /(^|: )error:/ { printf "%sFAIL  %s%s\n", red, $0, reset; fflush(); next }
    { print; fflush() }
  '
  statuses=("${PIPESTATUS[@]}")
  status=${statuses[0]}
  if (( status == 0 )); then
    status=${statuses[1]}
  fi

  if (( status == 0 )); then
    printf '%sPASS — %s exercises complete!%s\n' "$green" "$mode" "$reset"
  elif [[ $mode == optional ]]; then
    printf '%sOPTIONAL — incomplete; see diagnostics above. Required lab status is unchanged.%s\n' "$yellow" "$reset"
  else
    printf '%sFAIL — fix the required exercises above and rerun the lab.%s\n' "$red" "$reset"
  fi
  return "$status"
}

check_exercises "$1" required
required_status=$?
optional_file="$(dirname "$1")/optional/Skeleton.lean"
if [[ -f $optional_file ]]; then
  check_exercises "$optional_file" optional
fi
exit "$required_status"

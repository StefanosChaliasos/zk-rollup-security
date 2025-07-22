#!/bin/bash

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 N M"
  exit 1
fi

N="$1"
M="$2"
TEMPLATE="rollup_properties_template_N_M.als"
OUTPUT="rollup_properties_${N}_${M}.als"

if [ ! -f "$TEMPLATE" ]; then
  echo "Template file $TEMPLATE not found!"
  exit 2
fi

sed "s/{{N}}/$N/g; s/{{M}}/$M/g" "$TEMPLATE" > "$OUTPUT"

if [ $? -eq 0 ]; then
  echo "Generated $OUTPUT successfully."
else
  echo "Failed to generate $OUTPUT."
  exit 3
fi 
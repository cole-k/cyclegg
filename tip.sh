#!/bin/bash

# Specify the directory containing .smt2 files
directory="./examples/tip2015/isaplanner"
logdir="./examples/tip2015/isaplanner/logs"

# Check if the directory exists
if [ ! -d "$directory" ]; then
  echo "Error: Directory not found!"
  exit 1
fi

s=0
f=0

# Iterate through all .smt2 files in the directory
for file in "$directory"/*.smt2; do
  # Extract file name without extension
  filename=$(basename "$file" .smt2)
  
  # Run the command and save the output to a log file
  cargo run -- -v "$file" > "$logdir/$filename.log" 2>&1
  
  # Check the exit status of the command
  if [ $? -eq 0 ]; then
    echo "Success: $file"
    ((s++))
  else
    echo "Error: Failed to process $file"
    ((f++))
  fi
done

echo "Summary:"
echo "Successes: $s"
echo "Failures: $f"
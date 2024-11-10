#!/bin/bash

# Loop over all Fix*Filled.thy files
for FILE in FixSMDData*Filled.thy
do
    BASENAME=${FILE%.thy}
    echo "Processing $FILE"

    # Create subdirectory
    mkdir -p $BASENAME

    # Copy the .thy file into the subdirectory
    cp $FILE $BASENAME/

    # Create a ROOT file in the subdirectory
    cat > $BASENAME/ROOT <<EOF
session "$BASENAME" = BaseProof +
  options [document = false]
  theories
    $BASENAME
EOF

    # Build the session, capturing output and error messages
    echo "Building session $BASENAME"
    isabelle build -v -d . $BASENAME > $BASENAME/build_output.txt 2>&1

done

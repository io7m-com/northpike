#!/bin/sh

for f in $(ls Northpike/*.v | sort -u)
do
  ID=$(uuidgen -s -n @x500 -N "$f")

  cat <<EOF
  <FormalItem title="$f" id="${ID}">
    <Verbatim><xi:include href="$f" parse="text"/></Verbatim>
  </FormalItem>
EOF
done

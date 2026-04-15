#!/bin/bash
for i in $(ls  *.png)
do
convert $i -trim $i
done

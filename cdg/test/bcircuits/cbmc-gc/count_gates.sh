#!/bin/bash 
echo $1  
echo -e "AND\t OR\t XOR\t INV\t TOTAL"
cAND=$(cat $1 | grep " AND" | wc -l)
cOR=$(cat $1 | grep " OR"  | wc -l)
cXOR=$(cat $1 | grep " XOR" | wc -l)
cINV=$(cat $1 | grep " INV" | wc -l)
cILL=$(cat $1 | wc -l)
cTOTAL=$(expr $cILL - 3)
echo -e $cAND "\t" $cOR "\t" $cXOR "\t" $cINV "\t" $cTOTAL


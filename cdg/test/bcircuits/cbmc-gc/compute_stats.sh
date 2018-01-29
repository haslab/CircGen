for d in ./*; do
  if [ -d "$d" ]; then
    cd $d
    make clean
    make all
    #make count
    cd ..
  fi
done


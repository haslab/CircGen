import os
import sys
import glob
import csv

import lndir

txt = """
Makefile
Makefile.extr
backend
cfrontend
driver
extraction
ia32
arm
pg
tools

./backend:
RTLtyping.v

./cfrontend:
CPragmas.ml

./driver:
Compiler.v
Complements.v
Driver.ml

./extraction:
extraction.v

./ia32:
Machregsaux.ml

./tools:
MacOSXheaders

./tools/MacOSXheaders:
Availability.h
Availability.h.orig
sys

./tools/MacOSXheaders/sys:
cdefs.h
cdefs.h.orig
""".splitlines()


def parseLsR(src, dst):
    """
    Create a mirror directory for all file names readed from 'stdin'
    ("ls -R" format).
    
    :param src: src path, if relative, relative to dst not cwd
    :param dst: dst mpath, must exit.
    """
    dst = os.path.abspath(dst)
    if os.path.isabs(src):
        calculate_src = lambda ss, sd: ss
    else:
        # following the X11 lndir convention if src is relative,
        # it is relative to dst not to cwd.
        src = os.path.abspath(os.path.join(dst, src))
        calculate_src = os.path.relpath
    assert os.path.isdir(src), "src path is not a directory"
    assert os.path.isdir(dst), "dst path is not a directory"
    txt = sys.stdin.read()
    dir_prefix = "."
    for l in [l for l in txt.splitlines() if l]:
        if l[-1]==':':
            dir_prefix = l[:-1] 
            if not os.path.exists(os.path.join(dst,dir_prefix)):
                os.mkdir(os.path.join(dst,dir_prefix))
        else:
            file_name = os.path.join(dir_prefix,l)
            real_src = os.path.join(src,file_name)
            real_dst = os.path.join(dst,file_name)
            if os.path.isdir(real_src):
                if not os.path.exists(real_dst):
                    os.mkdir(real_dst)
                sym_src = calculate_src(real_src, real_dst)
                lndir.lndir(sym_src,real_dst)
            elif os.path.isfile(real_src):
                sym_src = calculate_src(real_src, os.path.join(dst,dir_prefix))
                lndir.delete_if_exists_and_overwrite(True,real_dst)
                lndir.improved_error_symlink(sym_src, real_dst)
            else:
                print("Unknow entry: ", file_name)



################################################################################
### Main logic and argument handling                                         ###
################################################################################

try:
  if __name__ == '__main__':
    ### check to see that all args are present on the command line            
    ##############################################################
    if len(sys.argv) < 3:
      print("Usage: %s <src>/ <dst>/" % sys.argv[0])
      sys.exit(1)
    else:
      ### check to see that source and destination targets exist
      ##########################################################
      src = str(sys.argv[1])
      dst = str(sys.argv[2])
      if not os.path.isdir(dst):
        raise OSError("ERROR: %s is not a valid directory." % dst)
      parseLsR(src,dst)
except OSError as msg:
  print(msg)
  sys.exit(0)

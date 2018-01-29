# based on a mix of the following two references...

# https://github.com/rbbratta/site_lib/blob/master/lndir.py

# Copyright (c) 2013, Mike 'Fuzzy' Partin <fuzzy@fu-manchu.org>
# http://code.activestate.com/recipes/578535-lndirpy-short-python-version-of-the-bsdx11-lndir-u/

#  Copyright(c) 2013 Intel Corporation.

# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice,
# this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
# The views and conclusions contained in the software and documentation are
# those of the authors and should not be interpreted as representing official
# policies, either expressed or implied, of the FreeBSD Project.


import os
import sys
import logging

logging.basicConfig(level=logging.DEBUG)


def print_verbose(dir_count, file_count, src_base):
    sys.stdout.write('%-53s %6d dirs %6d files\n' % (
        src_base[:52],  # basename of src
        dir_count,  # Dir count
        file_count))  # File count
    sys.stdout.flush()


def universal_basename(src):
    """
    Basename that works with paths that have a trailing slash.
    The normal basename doesn't do what we want when there is a trailing slash.
    e.g.  os.path.basename("/a/b/c/d/") returns '', we want 'd'
    So remove the trailing slash using normpath before running basename.

    :param src: src path with or without trailing slash
    :type src: str
    :return: basename
    :rtype: str
    """
    # normpath will remove trailing /
    return os.path.basename(os.path.normpath(src))


def calculate_src_dst(dst, src_filename, root, src):
    """

    :param dst: dst root
    :param src_filename: src filename
    :param root: os.walk root
    :param src: src root
    :return: symlink dst and symlink src
    :rtype: tuple
    """
    # relative dir always equals root - src
    # so remove src from the left of root.
    # abspath removes trailing / so just use '/'.join
    # don't use os.path.join because since root.split(src)[1]
    # is an abspath os.path.join will discard dst.
    # don't use lstrip, lstrip takes a set of chars, not a substring
    # root.split(src)[1] feels slightly better than
    # re.sub(src, '', root)
    sym_dst_dir = os.sep.join([dst, root.split(src)[1]])
    sym_dst = os.path.join(sym_dst_dir, src_filename)
    return sym_dst_dir, sym_dst


def delete_if_exists_and_overwrite(overwrite, sym_dst):
    if overwrite and os.path.islink(sym_dst):
        try:
            os.unlink(sym_dst)
        except OSError:
            logging.exception("Unable to remove %s", sym_dst)


def improved_error_symlink(sym_src, sym_dst):
    try:
        os.symlink(sym_src, sym_dst)
    except OSError:
        # The standard OSError message sucks
        logging.exception("src = %s, dst = %s", sym_src, sym_dst)
        raise OSError("%s exists = %s, %s exists = %s" % (sym_src,
                                                          os.path.exists(
                                                              sym_src),
                                                          sym_dst,
                                                          os.path.exists(sym_dst)))


def lndir(src, dst, overwrite=True, summary_print_func=None):
    """
    Create a recursive symlink shadow copy of src in dst.
    Directories in src will be created in dst.  All other files will be symlinked from dst to src.

    If the src is a symlink then the destination symlink will be re-linked to the origin target.

    :param src: src path, if relative, relative to dst not cwd
    :param dst: dst mpath, must exit.
    :param overwrite: defaul True, overwrite existing symlinks in dst
    :param summary_print_func: Function to print a summary after each interation
    :return: count of directores created and files symlinked
    :rtype: tuple
    """
    if summary_print_func is None:
        summary_print_func = lambda *args: None
    dst = os.path.abspath(dst)
    if os.path.isabs(src):
        calculate_src = lambda ss, sd: ss
    else:
        # following the X11 lndir convention if src is relative,
        # it is relative to dst not to cwd.
        src = os.path.abspath(os.path.join(dst, src))
        calculate_src = os.path.relpath

    # start walking the source target
    dir_c = 0  # counter for dires
    file_c = 0  # counter for files

    for root, dirs, files in os.walk(src):
        for f in files:
            real_src = os.path.join(root, f)
            sym_dst_dir, sym_dst = calculate_src_dst(dst, f, root, src)
            delete_if_exists_and_overwrite(overwrite, sym_dst)
            if os.path.islink(real_src):
                # assume relative symlink does not reach above src
                # and just use the original link
                sym_src = os.readlink(real_src)
                improved_error_symlink(sym_src, sym_dst)
            else:
                sym_src = calculate_src(os.path.join(root, f), sym_dst_dir)
                improved_error_symlink(sym_src, sym_dst)
            file_c += 1
        for d in dirs:
            real_src = os.path.join(root, d)
            sym_dst_dir, sym_dst = calculate_src_dst(dst, d, root, src)
            delete_if_exists_and_overwrite(overwrite, sym_dst)
            if os.path.islink(real_src):
                # assume relative symlink does not reach above src
                # and just use the original link
                sym_src = os.readlink(real_src)
                improved_error_symlink(sym_src, sym_dst)
            else:
                try:
                    os.mkdir(sym_dst)
                except OSError:
                    if not(os.path.isdir(sym_dst)):
                        logging.exception(" dst = %s", sym_dst)
            dir_c += 1
        summary_print_func(dir_c, file_c, root)
    return dir_c, file_c


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
            for i in [src, dst]:
                if not os.path.isdir(i):
                    raise OSError("ERROR: %s is not a valid directory." % i)
                lndir(src,dst)
except OSError as msg:
    print(msg)
    sys.exit(0)

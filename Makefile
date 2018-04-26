all:
	@echo \"make setup_build_dir\" - relinks CGT files on build dir
	@echo \"make clean_setup_build_dir\" - relinks both CompCert and CGT files

setup_build_dir: scripts/CDG.files
	@python scripts/setup_build.py ../cdg build < scripts/CDG.files

clean_setup_build_dir: scripts/CompCert.files scripts/CDG.files
	@rm -rf build/*
	@cp submodules/CompCert/.depend build/
	@python3 scripts/setup_build.py ../submodules/CompCert build < scripts/CompCert.files
	@python3 scripts/setup_build.py ../cdg build < scripts/CDG.files

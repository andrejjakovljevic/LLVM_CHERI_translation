# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local64/bin/cmake

# The command to remove a file.
RM = /usr/local64/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/aj658/LLVM_passes_new/LLVM_passes

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/aj658/LLVM_passes_new/LLVM_passes/build

# Utility rule file for install-HelloPass-stripped.

# Include any custom commands dependencies for this target.
include HelloPass/CMakeFiles/install-HelloPass-stripped.dir/compiler_depend.make

# Include the progress variables for this target.
include HelloPass/CMakeFiles/install-HelloPass-stripped.dir/progress.make

HelloPass/CMakeFiles/install-HelloPass-stripped:
	cd /home/aj658/LLVM_passes_new/LLVM_passes/build/HelloPass && /usr/local64/bin/cmake -DCMAKE_INSTALL_COMPONENT="HelloPass" -DCMAKE_INSTALL_DO_STRIP=1 -P /home/aj658/LLVM_passes_new/LLVM_passes/build/cmake_install.cmake

install-HelloPass-stripped: HelloPass/CMakeFiles/install-HelloPass-stripped
install-HelloPass-stripped: HelloPass/CMakeFiles/install-HelloPass-stripped.dir/build.make
.PHONY : install-HelloPass-stripped

# Rule to build all files generated by this target.
HelloPass/CMakeFiles/install-HelloPass-stripped.dir/build: install-HelloPass-stripped
.PHONY : HelloPass/CMakeFiles/install-HelloPass-stripped.dir/build

HelloPass/CMakeFiles/install-HelloPass-stripped.dir/clean:
	cd /home/aj658/LLVM_passes_new/LLVM_passes/build/HelloPass && $(CMAKE_COMMAND) -P CMakeFiles/install-HelloPass-stripped.dir/cmake_clean.cmake
.PHONY : HelloPass/CMakeFiles/install-HelloPass-stripped.dir/clean

HelloPass/CMakeFiles/install-HelloPass-stripped.dir/depend:
	cd /home/aj658/LLVM_passes_new/LLVM_passes/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/aj658/LLVM_passes_new/LLVM_passes /home/aj658/LLVM_passes_new/LLVM_passes/HelloPass /home/aj658/LLVM_passes_new/LLVM_passes/build /home/aj658/LLVM_passes_new/LLVM_passes/build/HelloPass /home/aj658/LLVM_passes_new/LLVM_passes/build/HelloPass/CMakeFiles/install-HelloPass-stripped.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : HelloPass/CMakeFiles/install-HelloPass-stripped.dir/depend

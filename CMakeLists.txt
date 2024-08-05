cmake_minimum_required(VERSION 3.20)
project(NuPBO_main)

set(CMAKE_CXX_STANDARD 11)

include_directories(source_code)
#set(CMAKE_CXX_FLAGS -O3)

add_executable(NuPBO_main
        basis_pms.cpp
        basis_pms.h
        cmdline.h
        heuristic.cpp
        heuristic.h
        init.cpp
        init.h
        main.cpp
        parse_arguments.cpp
        parse_arguments.h
        settings.cpp
        settings.h
        string_util.cpp
        string_util.h)

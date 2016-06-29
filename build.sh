#!/bin/bash
clang++ -stdlib=libc++ -std=c++11 -I/usr/local/include/ -L/usr/local/lib/ -lboost_graph collatz.cpp -o collatz
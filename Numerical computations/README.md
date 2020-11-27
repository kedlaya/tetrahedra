The C++ code was compiled using these commands:

```
g++ -I/usr/local/include -O3 -c -o tmp.o low_order_solutions.cc
libtool --tag=CXX --mode=link g++  -O3 -o low_order_solutions tmp.o -lqd
```

In case you do not have a working systemwide libtool, you may be able to use the one built during the QD compilation.
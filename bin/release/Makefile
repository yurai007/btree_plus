clang: CC := clang++
clang: CXXFLAGS = -Wall -Wextra -std=c++20 -Wno-c99-extensions -Wno-c++98-compat-pedantic -fcoroutines-ts -Ofast -march=native -g
clang: LDFLAGS = -lfmt -lbenchmark
clang: ../../src/btree_plus.cpp
	$(CC) $(CXXFLAGS) ../../src/btree_plus.cpp -o btree_cl $(LDFLAGS)	

gcc: CC := g++
gcc: CXXFLAGS = -Wall -W -Wextra -Wpedantic -Wformat-security -Walloca -Wduplicated-branches -std=c++20 -fconcepts -Ofast -march=native -g
gcc: LDFLAGS = -lfmt -lbenchmark
gcc: ../../src/btree_plus.cpp
	$(CC) $(CXXFLAGS) ../../src/btree_plus.cpp -o btree $(LDFLAGS)
clean:
	@- $(RM) btree btree_cl


tidy:
	clang-tidy ../../src/btree_plus.cpp

heavy: 
	make CXXFLAGS='-Wall -W -Wextra -Wpedantic -g -std=c++20 -fcoroutines-ts' clang && \
                valgrind --tool=helgrind ./btree_cl && valgrind --tool=memcheck --leak-check=yes --show-reachable=yes --num-callers=20 --track-fds=yes --expensive-definedness-checks=yes ./btree_cl 

distclean: clean

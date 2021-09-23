clang: CC := clang++
clang: CXXFLAGS = -Wall -Wextra -g -std=c++20 -Wno-c99-extensions -Wno-c++98-compat-pedantic 
# -stdlib=libc++ no std::ranges
clang: CXXFLAGS += -fsanitize=address -fsanitize-recover=address -fsanitize=undefined -fsanitize-address-use-after-scope -fsanitize=signed-integer-overflow -fsanitize=vptr
#clang: CXXFLAGS += -march=native
clang: ../../src/btree_plus.cpp
	$(CC) $(CXXFLAGS) ../../src/btree_plus.cpp -o btree_cl $(LDFLAGS)	

gcc: CC := g++
gcc: CXXFLAGS = -Wall -W -Wextra -Wpedantic -Wformat-security -Walloca -Wduplicated-branches -g -std=c++20 -fconcepts
gcc: CXXFLAGS += -fsanitize=address -fsanitize-recover=address -fsanitize=undefined -fsanitize-address-use-after-scope -fsanitize=signed-integer-overflow -fsanitize=vptr
#gcc: CXXFLAGS += -march=native
gcc: LDFLAGS = -lpthread
gcc: ../../src/btree_plus.cpp
	$(CC) $(CXXFLAGS) ../../src/btree_plus.cpp -o btree $(LDFLAGS)
clean:
	@- $(RM) btree btree_cl

distclean: clean

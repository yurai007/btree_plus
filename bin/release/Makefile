gcc: CC := g++
gcc: CXXFLAGS = -Wall -W -Wextra -Wpedantic -Wformat-security -Walloca -Wduplicated-branches -std=c++20 -fconcepts -Ofast -march=native
#gcc: CXXFLAGS += -fsanitize=address -fsanitize-recover=address -fsanitize=undefined -fsanitize-address-use-after-scope -fsanitize=signed-integer-overflow -fsanitize=vptr
gcc: LDFLAGS = -lpthread -lbenchmark
gcc: ../../src/main.cpp ../../src/rev3.cpp
	$(CC) $(CXXFLAGS) ../../src/main.cpp -o main $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/rev3.cpp -o rev3 $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/rev4.cpp -o rev4 $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/popcnt_stuff.cpp -o popcnt_stuff $(LDFLAGS)

clang: CC := clang
clang: CXXFLAGS = -Wall -W -Wextra -Wpedantic  -std=c++20 -Wno-c99-extensions -Wno-c++98-compat-pedantic -Ofast -march=native
#clang: CXXFLAGS += -stdlib=libc++
#clang: CXXFLAGS += -fsanitize=address -fsanitize-recover=address -fsanitize=undefined -fsanitize-address-use-after-scope -fsanitize=signed-integer-overflow -fsanitize=vptr
clang: LDFLAGS = -lbenchmark -lstdc++
clang: ../../src/main.cpp ../../src/rev3.cpp
#	$(CC) $(CXXFLAGS) ../../src/main.cpp -o main $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/rev3.cpp -o rev3 $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/rev4.cpp -o rev4 $(LDFLAGS)
	$(CC) $(CXXFLAGS) ../../src/popcnt_stuff.cpp -o popcnt_stuff_cl $(LDFLAGS)


clean:
	@- $(RM) main rev3 rev4 popcnt_stuff popcnt_stuff_cl


all:
	g++ -g -D_GLIBCXX_ASSERTIONS -O0 -o main cnf.cpp

run_debug: 
	g++ -g -O1 -fsanitize=address -fno-omit-frame-pointer -D_GLIBCXX_ASSERTIONS cnf.cpp -o main
	./main


run: all
	./main

clean:
	rm main
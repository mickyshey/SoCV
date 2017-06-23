CFLAGS = -std=c++11 -O3 -Wall
CFLAGS = -std=c++11 -g -Wall

seatAss: clean File.o Proof.o Solver.o seatAss.o seatMgr.o
	g++ -o $@ $(CFLAGS) File.o Proof.o Solver.o seatAss.o seatMgr.o

File.o: File.cpp
	g++ -c $(CFLAGS) File.cpp

Proof.o: Proof.cpp
	g++ -c $(CFLAGS) Proof.cpp

Solve.o: Solver.cpp
	g++ -c $(CFLAGS) Solver.cpp

seatAss.o: seatAss.cpp
	g++ -c $(CFLAGS) seatAss.cpp

seatMgr.o: seatMgr.cpp
	g++ -c $(CFLAGS) seatMgr.cpp

clean:
	rm -f *.o seatAss core* tags

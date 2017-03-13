default: makekeys
all: default

sm2.o: ../sm2.c ../sm2.h
	gcc -g -o sm2.o -c ../sm2.c

makekeys.o: makekeys.c ../sm2.h
	gcc -I.. -g -o makekeys.o -c makekeys.c

makekeys: sm2.o makekeys.o
	gcc -o makekeys makekeys.o sm2.o

clean:
	rm -f sm2.o makekeys.o makekeys

.PHONY: default all clean

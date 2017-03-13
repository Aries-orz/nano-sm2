all: test_sm2

sm2.o: sm2.c sm2.h
	$(CC) -c -o sm2.o sm2.c

%.o: %.c sm2.h
	$(CC) -c $< -o $@

test_sm2: test_sm2.o sm2.o
	$(CC) -o test_sm2 test_sm2.o sm2.o

clean:
	rm -f *.o test_sm2

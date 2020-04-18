all: compprac2

CC=g++
LD=g++
CFLAGS=-g -std=gnu++11 -Wall -Wextra -Iqbe/include
LDFLAGS=-Lqbe/lib

main.o: main.cpp
	$(CC) -c $(CFLAGS) $(LDFLAGS) $< -o $@

compprac2: main.o
	$(LD) $(CFLAGS) $(LDFLAGS) $^ -o $@ -lqbe

clean:
	rm -f main.o compprac2

%: input%.il compprac2
	./compprac2 < input$@.il

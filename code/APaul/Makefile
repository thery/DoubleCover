CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11
LDFLAGS = -lmpfr -lgmp -lm

TARGET = al

all: $(TARGET)

$(TARGET): al.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

clean:
	rm -f $(TARGET) *.o

.PHONY: all clean

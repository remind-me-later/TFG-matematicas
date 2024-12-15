.POSIX:

all: 
	tectonic -X build --keep-intermediates --keep-logs

clean:
	rm -rf build

.PHONY: all clean

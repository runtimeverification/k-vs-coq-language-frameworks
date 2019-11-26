SUBDIRS:=$(wildcard */.)

all: $(SUBDIRS)

all clean:
	@for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir -f Makefile $@; \
	done

.PHONY: all clean

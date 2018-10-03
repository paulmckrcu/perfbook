subdirs =  SMPdesign advsync count defer intro toolsoftrade locking
subdirs += datastruct/Issaquah datastruct/hash datastruct/log datastruct/skiplist

.PHONY: all clean pthreads

top := .
include depends.mk

all:
	for d in $(subdirs); \
	do \
		$(MAKE) -C $$d; \
	done

include recipes.mk

api.h Makefile.arch:
ifeq ($(strip $(target)),)
	$(MAKE) pthreads
	$(warning "Could not figure out which target arch to use (arch:$(arch)).")
else
	$(MAKE) pthreads
endif

pthreads:
	echo "#ifndef __PERFBOOK_API_H__" > api.h
	echo "#define __PERFBOOK_API_H__" >> api.h
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" >> api.h
	echo "" >> api.h
	cat linux/common.h >> api.h
	echo "" >> api.h
ifneq ($(strip $(target)),)
	cat arch-$(target)/arch-$(target).h >> api.h
	echo "" >> api.h
endif
	cat api-pthreads/api-pthreads.h | \
		sed '/begin{snippet}/d' | \
		sed '/end{snippet}/d' >> api.h
	echo "" >> api.h
	cat api-pthreads/api-gcc.h >> api.h
	echo "" >> api.h
	if test -f /usr/include/urcu-call-rcu.h -o \
		-f /usr/local/include/urcu-call-rcu.h -o \
		-f /usr/include/$(subdir_ub)/urcu-call-rcu.h ; \
	then \
		echo "#define _LGPL_SOURCE" >> api.h; \
		echo "#include <urcu/rculist.h>" >> api.h; \
		echo "#include <urcu/rcuhlist.h>" >> api.h; \
		echo "#include <urcu-pointer.h>" >> api.h; \
	elif test -d /usr/include/urcu -o -d /usr/local/include/urcu ; \
	then \
		echo "#define _LGPL_SOURCE" >> api.h; \
		echo "#include <urcu/rculist.h>" >> api.h; \
		echo "#include <urcu/rcuhlist.h>" >> api.h; \
		echo "#include <urcu-pointer-static.h>" >> api.h; \
	else \
		echo "### Missing liburcu package!!!  Install it. ###"; \
		exit 1;  \
	fi
	echo "#endif /* #ifndef __PERFBOOK_API_H__ */" >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	echo "" >> Makefile.arch
ifneq ($(strip $(target)),)
	cat arch-$(target)/Makefile.arch >> Makefile.arch
endif

clean:
	rm -f Makefile.arch api.h

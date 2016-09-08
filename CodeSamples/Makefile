all:
	(cd SMPdesign; make)
	(cd advsync; make)
	(cd count; make)
	(cd defer; make)
	(cd intro; make)
	(cd toolsoftrade; make)

pthreads:
	echo "#ifndef __PERFBOOK_API_H__" > api.h
	echo "#define __PERFBOOK_API_H__" >> api.h
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" >> api.h
	echo "" >> api.h
	cat linux/common.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	if test -f /usr/include/urcu-call-rcu.h -o -f /usr/local/include/urcu-call-rcu.h ; \
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
		cat linux/list.h >> api.h; \
	fi
	echo "#endif /* #ifndef __PERFBOOK_API_H__ */" >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch

pthreads-x86:
	echo "#ifndef __PERFBOOK_API_H__" > api.h
	echo "#define __PERFBOOK_API_H__" >> api.h
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" >> api.h
	echo "" >> api.h
	cat linux/common.h >> api.h
	echo "" >> api.h
	cat arch-x86/arch-x86.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-gcc.h >> api.h
	echo "" >> api.h
	if test -f /usr/include/urcu-call-rcu.h -o -f /usr/local/include/urcu-call-rcu.h ; \
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
		cat linux/list.h >> api.h; \
	fi
	echo "#endif /* #ifndef __PERFBOOK_API_H__ */" >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	echo "" >> Makefile.arch
	cat arch-x86/Makefile.arch >> Makefile.arch

pthreads-ppc64:
	echo "#ifndef __PERFBOOK_API_H__" >> api.h
	echo "#define __PERFBOOK_API_H__" >> api.h
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" >> api.h
	echo "" >> api.h
	cat linux/common.h >> api.h
	echo "" >> api.h
	cat arch-ppc64/arch-ppc64.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	if test -f /usr/include/urcu-call-rcu.h -o -f /usr/local/include/urcu-call-rcu.h ; \
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
		cat linux/list.h >> api.h; \
	fi
	echo "#endif /* #ifndef __PERFBOOK_API_H__ */" >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	cat arch-ppc64/Makefile.arch >> Makefile.arch

pthreads-arm:
	echo "#ifndef __PERFBOOK_API_H__" > api.h
	echo "#define __PERFBOOK_API_H__" >> api.h
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" >> api.h
	echo "" >> api.h
	cat linux/common.h >> api.h
	echo "" >> api.h
	cat arch-arm/arch-arm.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	if test -f /usr/include/urcu-call-rcu.h -o -f /usr/local/include/urcu-call-rcu.h ; \
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
		cat linux/list.h >> api.h; \
	fi
	echo "#endif /* #ifndef __PERFBOOK_API_H__ */" >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	cat arch-arm/Makefile.arch >> Makefile.arch

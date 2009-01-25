all:
	(cd SMPdesign; make)
	(cd advsync; make)

pthreads:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	cat linux/list.h >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch

pthreads-x86:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat arch-x86/arch-x86.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	cat linux/list.h >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	echo "" >> Makefile.arch
	cat arch-x86/Makefile.arch >> Makefile.arch

pthreads-ppc64:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat arch-ppc64/arch-ppc64.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h
	echo "" >> api.h
	cat linux/list.h >> api.h
	echo "# MECHANICALLY GENERATED, DO NOT EDIT!!!" > Makefile.arch
	echo "" >> Makefile.arch
	cat arch-ppc64/Makefile.arch >> Makefile.arch

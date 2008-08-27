all:
	(cd SMPdesign; make)
	(cd advsync; make)

pthreads:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h

pthreads-x86:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat arch-x86/arch-x86.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h

pthreads-ppc64:
	echo "/* MECHANICALLY GENERATED, DO NOT EDIT!!! */" > api.h
	echo "" >> api.h
	cat arch-ppc64/arch-ppc64.h >> api.h
	echo "" >> api.h
	cat api-pthreads/api-pthreads.h >> api.h

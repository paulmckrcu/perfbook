ifeq ($(strip $(arch)),)
arch := $(shell uname -m)
endif

ifeq ($(arch),i686)
target := x86
subdir_ub := i386-linux-gnu
else ifeq ($(arch),x86_64)
target := x86
subdir_ub := x86_64-linux-gnu
else ifeq ($(arch),ppc64)
target := ppc64
subdir_ub :=
else ifeq ($(arch),ppc64le)
target := ppc64
subdir_ub := powerpc64le-linux-gnu
else ifeq ($(arch),aarch64)
target := arm64
subdir_ub := aarch64-linux-gnu
else ifneq (,$(findstring arm,$(arch)))
target := arm
subdir_ub := arm-linux-gnueabihf
else
target :=
subdir_ub :=
endif

api_depend_common := $(top)/linux/common.h \
	$(top)/api-pthreads/api-pthreads.h \
	$(top)/api-pthreads/api-gcc.h

ifeq ($(target),x86)
api_depend := $(top)/arch-x86/arch-x86.h
arch_depend := $(top)/arch-x86/Makefile.arch
else ifeq ($(target),ppc64)
api_depend := $(top)/arch-ppc64/arch-ppc64.h
arch_depend := $(top)/arch-ppc64/Makefile.arch
else ifeq ($(target),arm)
api_depend := $(top)/arch-arm/arch-arm.h
arch_depend := $(top)/arch-arm/Makefile.arch
else ifeq ($(target),arm64)
api_depend := $(top)/arch-arm64/arch-arm64.h
arch_depend := $(top)/arch-arm64/Makefile.arch
else
api_depend :=
arch_depend :=
endif

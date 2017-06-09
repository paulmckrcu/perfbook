ifneq ($(top),.)
$(top)/api.h: $(api_depend) $(api_depend_common)
	$(MAKE) -C $(top) api.h

$(top)/Makefile.arch: $(arch_depend)
	$(MAKE) -C $(top) Makefile.arch
else
$(top)/api.h: $(api_depend) $(api_depend_common)
$(top)/Makefile.arch: $(arch_depend)
endif

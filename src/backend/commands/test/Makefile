subdir=src/backend/commands
top_builddir=../../../..
include $(top_builddir)/src/Makefile.global

TARGETS=tablecmds explain

include $(top_builddir)/src/backend/mock.mk

tablecmds.t: \
	$(MOCK_DIR)/backend/access/aocs/aocs_compaction_mock.o

explain.t: \
	$(MOCK_DIR)/backend/utils/cache/lsyscache_mock.o

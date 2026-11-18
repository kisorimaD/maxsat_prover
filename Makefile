CXX = g++
CXXFLAGS = -std=c++17 -Iinclude
LDFLAGS = 

EXE = maxsat_prover
SRCDIR = src
BINDIR = obj
TEST_EXE = $(BINDIR)/cpp_tests

OBJECTS = $(patsubst $(SRCDIR)/%.cpp,$(BINDIR)/%.o,$(wildcard $(SRCDIR)/*.cpp))
CORE_OBJECTS = $(filter-out $(BINDIR)/main.o $(BINDIR)/cli.o,$(OBJECTS))

all: $(EXE)

$(EXE): $(OBJECTS)
	$(CXX) $(OBJECTS) -g -O3 -o $(EXE) $(LDFLAGS)
	
$(BINDIR)/%.o: $(SRCDIR)/%.cpp | $(BINDIR)
	$(CXX) $(CXXFLAGS) -g -O3 -c -MMD -MP -o $@ $<

$(BINDIR)/cpp_tests.o: tests/cpp_tests.cpp | $(BINDIR)
	$(CXX) $(CXXFLAGS) -g -O3 -c -MMD -MP -o $@ $<

$(TEST_EXE): $(CORE_OBJECTS) $(BINDIR)/cpp_tests.o
	$(CXX) $^ -g -O3 -o $@ $(LDFLAGS)

-include $(OBJECTS:.o=.d) $(BINDIR)/cpp_tests.d

$(BINDIR):
	mkdir -p $(BINDIR)

clean:
	rm -rf $(BINDIR) $(EXE)

check: $(EXE) $(TEST_EXE)
	./$(TEST_EXE)
	python3 -m unittest discover -s tests -v

certificate: $(EXE)
	./$(EXE) interactive < solve.txt
	python3 stitch_certificate.py pre_certificate.jsonl proof_tree.json
	python3 verify_certificate.py proof_tree.json

.PHONY: clean all check certificate

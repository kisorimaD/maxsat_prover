CXX = g++
CXXFLAGS = -std=c++17 -Iinclude
LDFLAGS = 

EXE = maxsat_prover
SRCDIR = src
BINDIR = obj

OBJECTS = $(patsubst $(SRCDIR)/%.cpp,$(BINDIR)/%.o,$(wildcard $(SRCDIR)/*.cpp))

all: $(EXE)

$(EXE): $(BINDIR) $(OBJECTS)
	$(CXX) $(OBJECTS) -g -O3 -o $(EXE) $(LDFLAGS)
	
$(BINDIR)/%.o: $(SRCDIR)/%.cpp
	$(CXX) $(CXXFLAGS) -g -O3 -c -MMD -o $@ $<

include $(wildcard $(BINDIR)/*.d)

$(BINDIR):
	mkdir -p $(BINDIR)

clean:
	rm -rf $(BINDIR) $(EXE)

check: $(EXE)
	@set -e; for test in basic factor weight cache cover reductions safety step51; do ./$(EXE) $$test; done
	python3 -m unittest discover -v

certificate: $(EXE)
	./$(EXE) test < solve.txt
	python3 stitch_certificate.py pre_certificate.jsonl proof_tree.json
	python3 verify_certificate.py proof_tree.json

.PHONY: clean all check certificate

##
## K-vs-Coq Example: K make file
## Runtime Verification Inc.
##

## User Configuration (Specify the home directory of K)
K_HOME:=~/Github/k
export K_HOME

# Settings
# --------

BUILD_DIR:=.build
DEFN_DIR:=$(BUILD_DIR)/defn

K_RELEASE := $(K_HOME)/k-distribution/target/release/k
K_BIN     := $(K_RELEASE)/bin
K_LIB     := $(K_RELEASE)/lib
export K_RELEASE

MAIN_MODULE    := IMP
SYNTAX_MODULE  := IMP-SYNTAX
MAIN_DEFN_FILE := imp

KOMPILE_OPTS   :=

k_files := $(MAIN_DEFN_FILE).k

haskell_dir := $(DEFN_DIR)/haskell
java_dir    := $(DEFN_DIR)/java

haskell_kompiled := $(haskell_dir)/$(MAIN_DEFN_FILE)-kompiled/definition.kore
java_kompiled    := $(java_dir)/$(MAIN_DEFN_FILE)-kompiled/timestamp

# Rules
# -----

.PHONY: all default clean 					\
	build build-haskell build-java				\
	run-sum run-sum-haskell run-sum-java			\
	verify-sum verify-sum-haskell verify-sum-java		

default: all

all: verify-sum-java

clean:
	$(info K: Cleaning up ...)
	@rm -rf $(BUILD_DIR)

# Building
# --------

build: build-java
build-haskell: $(haskell_kompiled)
build-java:    $(java_kompiled)

# Haskell Backend

$(haskell_kompiled): $(k_files)
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell              \
                         --syntax-module $(SYNTAX_MODULE) $(MAIN_DEFN_FILE).k                \
                         --directory $(haskell_dir) -I $(haskell_dir)                        \
      	                 #--emit-json                                                         \
                         $(KOMPILE_OPTS)

# Java Backend

$(java_kompiled): $(java_files)
	$(info K: Building IMP binaries using kompile...)
	@$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend java              \
                         --syntax-module $(SYNTAX_MODULE) $(MAIN_DEFN_FILE).k             \
                         --directory $(java_dir) -I $(java_dir)				  \
                         #--emit-json                                                      \
                         $(KOMPILE_OPTS)

# Running SUM
# -----------
SUM_DIR:=sum
SUM_FILE:=$(SUM_DIR)/sum.imp

run-sum: run-sum-java

# Haskell Backend

run-sum-haskell: $(SUM_FILE) $(haskell_kompiled)
	$(K_BIN)/krun --directory $(haskell_dir) $(SUM_FILE)

# Java Backend

run-sum-java: $(SUM_FILE) $(java_kompiled)
	$(info K: Running the program SUM using krun...)
	@$(K_BIN)/krun --directory $(java_dir) $(SUM_FILE)


# Proving SUM's correctness
# -------------------------

SUM_SPEC:=$(SUM_DIR)/sum-spec.k

verify-sum: verify-sum-java

# Haskell Backend (NOTE: not yet supported)

verify-sum-haskell: $(SUM_SPEC) $(SUM_FILE) $(haskell_kompiled)
	$(K_BIN)/kprove --directory $(haskell_dir) $(SUM_SPEC)

# Java  Backend

verify-sum-java: $(SUM_SPEC) $(SUM_FILE) $(java_kompiled)
	$(info K: Verifying the correctness property of SUM using kprove...)
	@time -p $(K_BIN)/kprove --directory $(java_dir) $(SUM_SPEC)



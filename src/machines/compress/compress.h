// The compression machine (DESIGN.md): proof blocks in, each written smaller when the smaller block passes the
// checker's own execute_proof, else as given.
#pragma once

#include <cstddef>
#include <cstdio>
#include <ostream>

#include "src/runtime/runtime.h"
#include "src/util/error.h"

namespace logic::compress {

struct Stats {
    size_t blocks = 0;
    size_t as_given = 0;  // written as given: failing as given, or its rewrite failing
    size_t steps_in = 0;
    size_t steps_out = 0;
};

// Writes each proof block read from `in` to `out`. `rt` holds the dependencies and the header, and gains each block's
// claim as proof_checker registers it: proved, or unproved when the block fails as given.
util::ResultStatus compress(Runtime& rt, std::FILE* in, std::ostream& out, Stats& stats);

}  // namespace logic::compress

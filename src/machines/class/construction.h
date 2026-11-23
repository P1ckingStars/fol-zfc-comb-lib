// The construction: a class-existence claim for a formula, and its proof in plain fol-zfc steps (DESIGN.md §3, §4).
#pragma once

#include <map>
#include <string>
#include <utility>
#include <vector>

#include "src/machines/class/ast.h"

namespace cls {

enum class Shape { Class, Exact, Val, Set };

// A @def: P(binders) <-> body, its quantifiers not yet checked for guards.
struct Def {
    std::string axiom;
    std::vector<std::string> binders;
    Ptr body;
};

struct Request {
    Shape shape;
    std::string var;                                   // the abstracted variable
    std::vector<std::pair<std::string, bool>> params;  // each parameter, true if a set
    Ptr formula;                                       // free in var and the parameters
};

struct Output {
    std::string name;       // Cls.<SHAPE>_<fp>
    std::string statement;  // the claim's formula
    std::string proof;      // the proof block
};

// Throws Refused for a formula outside the gate.
Output construct(const Request& req, const std::map<std::string, Def>& defs);

}  // namespace cls

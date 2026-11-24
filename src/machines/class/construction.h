// The construction: a class-existence claim for a formula, and its proof in plain fol-zfc steps (DESIGN.md §3, §4).
#pragma once

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "src/machines/class/ast.h"

namespace cls {

enum class Shape { Class, Exact, Val, Set, Row };

// A @def: P(binders) <-> body, its quantifiers not yet checked for guards.
struct Def {
    std::string axiom;
    std::vector<std::string> binders;
    Ptr body;
};

// A row a formula is read through: the claim stating it, the formula and its places (DESIGN.md §10, decision 7).
struct Row {
    std::string claim;
    Ptr psi;
    std::vector<std::string> places;
};

struct Request {
    Shape shape;
    std::string var;                                   // the abstracted variable
    std::vector<std::pair<std::string, bool>> params;  // each parameter, true if a set
    Ptr formula;                                       // free in var and the parameters
    std::vector<std::string> vars;                     // ROW: the predicate's places, in order
};

struct Output {
    std::string name;       // Cls.<SHAPE>_<fp>
    std::string statement;  // the claim's formula
    std::string proof;      // the proof block
};

// Throws Refused for a formula outside the gate.
Output construct(const Request& req, const std::map<std::string, Def>& defs, const std::vector<Row>& rows);

// The row of psi over its places, 1 to 4 of them, in the form read1, read2 or read4 reads.
std::string row_statement(const Ptr& psi, const std::vector<std::string>& places);

// The row f states, if it states one; its claim left for the caller.
std::optional<Row> as_row(const Ptr& f);

}  // namespace cls

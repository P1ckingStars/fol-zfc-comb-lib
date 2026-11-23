// The class machine's formulas: fol-zfc formulas with named variables, read from src/core's IR.
#pragma once

#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/core/formula.h"

namespace cls {

// A formula outside the gate: no claim, no proof, only this reason.
struct Refused : std::runtime_error {
    using std::runtime_error::runtime_error;
};

enum class K { Atom, Pred, False, Not, And, Or, Imp, Iff, All, Ex, Forall, Exists };

struct Node;
using Ptr = std::shared_ptr<const Node>;

// Atom: elem, eq, set, zero, nsucc, snoc, each read by a row of its own. Pred: any other predicate.
// All and Ex are the guarded quantifiers; Forall and Exists are unguarded ones, refused at the gate.
struct Node {
    K k;
    std::string name;               // the predicate, or the bound variable
    std::vector<std::string> args;  // the predicate's arguments
    Ptr a, b;
};

bool is_atom(const std::string& name, size_t arity);

Ptr atom(const std::string& name, std::vector<std::string> args);
Ptr unary(K k, Ptr a);
Ptr binary(K k, Ptr a, Ptr b);
Ptr quant(K k, const std::string& v, Ptr body);

// Fresh names for bound variables.
class Fresh {
public:
    explicit Fresh(std::string prefix) : prefix_(std::move(prefix)) {}
    std::string operator()() { return prefix_ + std::to_string(++n_); }

private:
    std::string prefix_;
    int n_ = 0;
};

// A formula of the IR, its de Bruijn variables named: `names` holds the names in scope, innermost last.
Ptr from_ir(const logic::Formula& f, std::vector<std::string>& names, Fresh& fresh);

// Guarded quantifiers become All and Ex; an unguarded quantifier is refused.
Ptr guard(const Ptr& f);

// Free variables replaced by `m`; every bound variable renamed fresh.
Ptr rename(const Ptr& f, const std::map<std::string, std::string>& m, Fresh& fresh);

// Free variables replaced by `m`, bound names kept.
Ptr subst(const Ptr& f, const std::map<std::string, std::string>& m);

// The formula in fol-zfc syntax, fully parenthesized.
std::string print(const Ptr& f);

}  // namespace cls

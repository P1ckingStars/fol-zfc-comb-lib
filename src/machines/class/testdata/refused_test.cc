// The gate refuses, and says why: no claim for a formula outside it.
#include <iostream>

#include "src/machines/class/construction.h"

namespace {

bool refused(const cls::Ptr& f, std::vector<std::pair<std::string, bool>> params, const std::string& why) {
    cls::Request req{cls::Shape::Set, "x", std::move(params), f};
    try {
        cls::construct(req, {}, {});
    } catch (const cls::Refused& r) {
        if (std::string(r.what()).find(why) != std::string::npos) return true;
        std::cerr << "refused for another reason: " << r.what() << "\n";
        return false;
    }
    std::cerr << "not refused: " << cls::print(f) << "\n";
    return false;
}

}  // namespace

int main() {
    using namespace cls;
    bool ok = true;
    // forall y. elem(y, x): the quantifier ranges over classes.
    ok &= refused(quant(K::Forall, "y", atom("elem", {"y", "x"})), {}, "without its set guard");
    // elem(Q, x), Q a class parameter on a membership's left side.
    ok &= refused(atom("elem", {"Q", "x"}), {{"Q", false}}, "outside a membership's right side");
    // elem(y, x) with y neither in scope nor a parameter.
    ok &= refused(atom("elem", {"y", "x"}), {}, "free and no parameter");
    // A predicate with no @def.
    ok &= refused(atom("Unknown.p", {"x"}), {}, "no @def");
    return ok ? 0 : 1;
}

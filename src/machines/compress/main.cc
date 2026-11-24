// The compression machine's command line (DESIGN.md): a proof file's blocks written smaller to OUT, the dependencies and
// the header loaded as proof_checker loads them.
//
//   fol_compress OUT HEADER.fol.def PROOF.fol.proof [DEP.fol.lib|DEP.fol.def ...] [-- DEP.fol.proof ...]
#include <cstdio>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "src/machines/compress/compress.h"
#include "src/runtime/runtime.h"

namespace {

bool load(logic::Runtime& rt, const std::string& path) {
    if (path.size() >= 8 && path.substr(path.size() - 8) == ".fol.lib") {
        auto st = rt.load_library(path);
        if (st.ok()) return true;
        std::cerr << "cannot load " << path << ": " << st.error().to_string() << "\n";
        return false;
    }
    auto r = rt.load_file_recursive(path);
    if (!r.ok()) {
        std::cerr << "cannot load " << path << ": " << r.error().to_string() << "\n";
        return false;
    }
    auto ran = rt.execute_all_proofs(r.value());
    if (ran.ok()) return true;
    std::cerr << "cannot run the proofs of " << path << ": " << ran.error().to_string() << "\n";
    return false;
}

}  // namespace

int main(int argc, char* argv[]) {
    if (argc < 4) {
        std::cerr << "usage: fol_compress OUT HEADER.fol.def PROOF.fol.proof [DEP ...] [-- DEP.fol.proof ...]\n";
        return 1;
    }
    std::vector<std::string> deps, dep_proofs;
    bool after = false;
    for (int i = 4; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--") after = true;
        else (after ? dep_proofs : deps).push_back(a);
    }
    logic::Runtime rt;
    for (const auto& d : deps)
        if (!load(rt, d)) return 1;
    for (const auto& d : dep_proofs)
        if (!load(rt, d)) return 1;
    if (!load(rt, argv[2])) return 1;

    std::FILE* in = std::fopen(argv[3], "r");
    if (!in) {
        std::cerr << "cannot open " << argv[3] << "\n";
        return 1;
    }
    std::ofstream out(argv[1]);
    logic::compress::Stats stats;
    auto st = logic::compress::compress(rt, in, out, stats);
    std::fclose(in);
    if (!st.ok()) {
        std::cerr << "fol_compress: " << st.error().to_string() << "\n";
        return 1;
    }
    std::cout << stats.blocks << " blocks, " << stats.as_given << " as given; steps " << stats.steps_in << " -> "
              << stats.steps_out << "\n";
    return 0;
}

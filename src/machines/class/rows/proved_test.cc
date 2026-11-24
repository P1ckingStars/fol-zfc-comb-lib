// Every row is on proof_checker's Proved list: each count file says one claim proved, none conditional or unproved.
#include <fstream>
#include <iostream>
#include <map>
#include <string>

int main(int argc, char** argv) {
    bool ok = argc > 1;
    for (int i = 1; i < argc; ++i) {
        std::ifstream in(argv[i]);
        std::map<std::string, long> count;
        for (std::string key; in >> key;) in >> count[key];
        bool good = count["proved:"] == 1 && count["conditional:"] == 0 && count["unproved:"] == 0;
        if (!good) std::cerr << "FAILED: " << argv[i] << "\n";
        ok = ok && good;
    }
    return ok ? 0 : 1;
}

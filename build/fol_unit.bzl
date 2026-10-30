"""A translated unit (`isa2fol lower --emit`) as a repository of fol_proof targets."""

def _fol_unit_impl(rctx):
    unit = rctx.getenv("FOL_UNIT") or "%s/isa2fol-units/%s/unit" % (rctx.getenv("HOME"), rctx.attr.dir)
    root = rctx.path(unit)
    if not root.get_child("parts").exists:
        fail("no translated unit at %s; set FOL_UNIT or see lib/README.md" % unit)

    # The unit is generated and stays out of git; the manifest pins every file of it.
    check = rctx.execute(
        ["sha256sum", "--check", "--quiet", "--strict", str(rctx.path(rctx.attr.manifest))],
        working_directory = unit,
    )
    if check.return_code != 0:
        fail("%s does not match %s:\n%s%s" % (unit, rctx.attr.manifest, check.stdout, check.stderr))

    names = []
    rules = []
    for line in rctx.read(root.get_child("parts")).splitlines():
        name, _, cited = line.partition(":")
        names.append(name)
        for suffix in [".fol.def", ".fol.proof"]:
            rctx.symlink(root.get_child(name + suffix), name + suffix)
        deps = ['"@@//lib:base"'] + ['":%s"' % part for part in cited.split(" ") if part]
        rules.append(
            'fol_proof(name = "%s", header = "%s.fol.def", proof = "%s.fol.proof", deps = [%s])' %
            (name, name, name, ", ".join(deps)),
        )

    rctx.file("BUILD.bazel", "\n".join([
        'load("@@//build:fol.bzl", "fol_group", "fol_proof")',
        'package(default_visibility = ["//visibility:public"])',
        'fol_group(name = "parts", deps = [%s])' % ", ".join(['":%s"' % name for name in names]),
    ] + rules) + "\n")

fol_unit = repository_rule(
    implementation = _fol_unit_impl,
    attrs = {
        "dir": attr.string(mandatory = True, doc = "The unit's directory under ~/isa2fol-units."),
        "manifest": attr.label(mandatory = True, doc = "sha256sum of the unit's parts file, headers and proofs."),
    },
    doc = "One fol_proof per part, citing the parts its `parts` line names, and a group of them all.",
)

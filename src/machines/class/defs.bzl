"""class_claim: the class machine run on a request at build time, its claim and proof for a fol_proof; fol_group: checked
parts as one dependency."""

load("//build:fol.bzl", "FolInfo")

def _class_claim_impl(ctx):
    libs = depset(transitive = [d[FolInfo].libs for d in ctx.attr.deps + ctx.attr.rows], order = "postorder")
    args = ctx.actions.args()
    args.add(ctx.file.request)
    args.add(ctx.outputs.out_def)
    args.add(ctx.outputs.out_proof)
    args.add_all(libs)
    ctx.actions.run_shell(
        outputs = [ctx.outputs.out_def, ctx.outputs.out_proof],
        inputs = depset([ctx.file.request], transitive = [libs]),
        tools = [ctx.executable._machine],
        command = '"$@" > /dev/null',
        arguments = [ctx.executable._machine.path, args],
        mnemonic = "ClassMachine",
        progress_message = "Class machine on %{label}",
    )
    return [DefaultInfo(files = depset([ctx.outputs.out_def, ctx.outputs.out_proof]))]

class_claim = rule(
    implementation = _class_claim_impl,
    attrs = {
        "request": attr.label(allow_single_file = True, mandatory = True),
        "deps": attr.label_list(providers = [FolInfo], doc = "The parts the formula's constants and @defs come from."),
        "rows": attr.label_list(
            providers = [FolInfo],
            default = ["//src/machines/class/rows"],
            doc = "The rows the machine reads defined predicates through (DESIGN.md §10, decision 5).",
        ),
        "out_def": attr.output(mandatory = True),
        "out_proof": attr.output(mandatory = True),
        "_machine": attr.label(
            default = "//src/machines/class:class_machine",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _fol_group_impl(ctx):
    libs = depset(order = "postorder", transitive = [d[FolInfo].libs for d in ctx.attr.deps])
    return [
        FolInfo(
            headers = depset(transitive = [d[FolInfo].headers for d in ctx.attr.deps]),
            proofs = depset(transitive = [d[FolInfo].proofs for d in ctx.attr.deps]),
            lib = None,
            libs = libs,
        ),
        DefaultInfo(files = libs),
    ]

fol_group = rule(
    implementation = _fol_group_impl,
    attrs = {"deps": attr.label_list(providers = [FolInfo])},
)

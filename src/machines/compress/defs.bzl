"""fol_compress: a proof file written smaller by the compression machine (DESIGN.md), for a fol_proof to check;
fol_compressed_proof: the two together."""

load("//build:fol.bzl", "FolInfo", "fol_proof")

def _fol_compress_impl(ctx):
    libs = depset(order = "postorder", transitive = [d[FolInfo].libs for d in ctx.attr.deps])
    headers = depset(transitive = [d[FolInfo].headers for d in ctx.attr.deps])
    out = ctx.actions.declare_file(ctx.label.name + ".fol.proof")
    args = ctx.actions.args()
    args.add(out)
    args.add(ctx.file.header)
    args.add(ctx.file.proof)
    args.add_all(libs)
    ctx.actions.run_shell(
        outputs = [out],
        inputs = depset([ctx.file.header, ctx.file.proof], transitive = [libs, headers]),
        tools = [ctx.executable._compress],
        command = '"$@" > /dev/null',
        arguments = [ctx.executable._compress.path, args],
        mnemonic = "FolCompress",
        progress_message = "Compressing %{label}",
    )
    return [DefaultInfo(files = depset([out]))]

fol_compress = rule(
    implementation = _fol_compress_impl,
    attrs = {
        "header": attr.label(allow_single_file = [".fol.def"], mandatory = True),
        "proof": attr.label(allow_single_file = [".fol.proof"], mandatory = True),
        "deps": attr.label_list(providers = [FolInfo], doc = "As the fol_proof that checks the output."),
        "_compress": attr.label(
            default = "//src/machines/compress:fol_compress",
            executable = True,
            cfg = "exec",
        ),
    },
)

def fol_compressed_proof(name, header, proof, deps = [], **kwargs):
    """A fol_proof of the proof written smaller: `name` checks it, `name + "_compressed"` writes it."""
    fol_compress(name = name + "_compressed", header = header, proof = proof, deps = deps)
    fol_proof(name = name, header = header, proof = ":" + name + "_compressed", deps = deps, **kwargs)

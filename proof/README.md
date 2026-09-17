# Finite Proof Package

This is an offline scientific snapshot. Paths follow mathematical roles:

~~~text
assets/quotients/   Upstream certificate, lookup tables and quotient utilities
assets/occupation/ Integer-row semantics, Boolean-copy encoders and eight proofs
assets/structural/ Separate unary encoders and structural checks
~~~

The entry point is verify_proof_package.py. Run the Make targets from the
repository root. The manifest binds each transformed source and each
unchanged binary certificate to a hash.

The [cache metadata record](../evidence/cache-metadata.json) documents certificate
paths and cache identities. Tensor arrays, lookup payloads, CNF formulas and DRAT
proof bytes are preserved. The [verification record](../evidence/verification.json)
reports a replay of the published proof inputs.

The primary route regenerates eight CNFs and checks eight frozen DRAT proofs.
The separate transparent-unary route is preserved as additional evidence;
a primary replay is not a claim to have rerun that entire second route.

Historical diagnostic JSON files remain historical. Fresh checks use a new
output directory and require successful child execution plus valid new
result data. Neither a recorded success nor a solver timeout proves a theorem.

The written proof and the mathematical meaning of the encoding remain part
of the trusted argument; this package is not a formal proof assistant kernel.

This directory contains the CNF/DRAT proof package. The complete
[Lean formalization](../formalization/README.md) is maintained separately in
`formalization/`; it connects the finite premises and structural argument
within the proof assistant.

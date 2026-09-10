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

Scientific filenames replace the private preparation paths. Text metadata
has been sanitized; tensor arrays, lookup payloads, CNF formulas and DRAT
proof bytes have not been rewritten. The transformed bundle must pass its
own fresh replay before its release receipt can claim success.

The primary route regenerates eight CNFs and checks eight frozen DRAT proofs.
The separate transparent-unary route is preserved as additional evidence;
a primary replay is not a claim to have rerun that entire second route.

Historical diagnostic JSON files remain historical. Fresh checks use a new
output directory and require successful child execution plus valid new
result data. Neither a recorded success nor a solver timeout proves a theorem.

The written proof and the mathematical meaning of the encoding remain part
of the trusted argument; this package is not a formal proof assistant kernel.

No Lean formalization is included. The theorem is supported by the written
algebraic proof and the computational certificates described above. The
packaged scripts reproduce the finite premises; they do not replace the
written proof with a proof-assistant derivation.

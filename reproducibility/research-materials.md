# Using the Research Materials

There are two different reproducibility surfaces in this repository.

**The maintained proof package** has a documented entry point, frozen inputs,
independent encoding checks and proof replay. Follow [README.md](README.md).

**The exploratory archive** records programs, hypotheses, calculations and
results that informed the investigation. It is organized by mathematical topic
under [research/materials](../research/materials/README.md). These are historical
artifacts, not additional tests that run automatically with the final proof.

## What the Release Checks

- Every included artifact has a size and SHA256 identity in the catalog and
  release manifest.
- Included JSON is parsed; numerical arrays are inspected without enabling
  pickle deserialization. Empty, truncated or unsupported objects are not
  silently promoted to valid data.
- Python sources are syntax-checked, not imported or executed during catalog
  validation. Import-time execution can launch a search or write files.
- Research identifiers and machine-specific references are removed from the
  public copies, including embedded cache metadata. Mathematical data are
  preserved; the [redaction receipt](../evidence/cache-metadata-redaction.json)
  distinguishes changed labels from unchanged numerical payloads. A fresh
  proof replay checks the resulting public files.
- The maintained PDF, LaTeX source archive and repository archive are checked
  as separate release artifacts.

These are packaging and structural checks. They do not establish that every
historical theorem, recorded solver status or exploratory program is correct.

## Reusing an Exploratory Program

Read its linked notes, scientific inputs and dependencies first. Work in a
fresh directory or isolated environment; never run the entire archive as a
test suite. Historical sources may require additional libraries, replacement
of data paths, reconstruction of a large search input, or an explicitly chosen
resource limit. Their archived names and references are scientific rather than
original execution identifiers; they are not all maintained command-line tools.

For a new run, keep the archived inputs read-only and write results to a new
directory. Record the exact code, parameters, inputs, environment and new
outputs. Compare numerical identities or certificates, not only status strings.
Do not overwrite a historical result with a new run's output.

## Coverage

The catalog distinguishes notes, plans, implementation sources, result records
and numeric arrays. It includes research from all parts of the investigation,
not only material used in the final theorem. The coverage receipt states the
included counts and the categories intentionally left out.

Bulk exploratory search formulas, duplicate intermediate proof traces,
large restart caches, incomplete files and external downloaded publications are
not an unreviewed appendage to this release. The final theorem's certificate
inputs remain in proof/, independently of those exclusions. Third-party
constructions and methods retain their attribution; the project does not
relicense upstream work. Consult [LICENSE](../LICENSE).

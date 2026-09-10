# Linear Completion Structural Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key Finding: Outer-Product Column-Space Obstruction

### Setup
For fixed A-masks {a₁,...,a₂₂} and proposed B-masks {b₁,...,b₂₂}, define:
- K = [a₁⊗b₁ | ... | a₂₂⊗b₂₂] (81×22 matrix over F₂)
- D = tensor flattening of T_{⟨3,3,3⟩} (81×9, rank 9 over F₂)
- C exists iff col(D) ⊂ col(K), and is determined by linear algebra

### Result 1: Random B is Hopeless
For ALL tested A-multisets (rank-23 deletions AND peer Wang-admissible):
- dim(span(A)) = 9 (full), so V_A = span{a_t⊗e_j} = F₂^81 (full 81D)
- Yet random B always gives D-defect = 9 (maximum: NO D-column in col(K))
- Only the rank-23 B-factors give defect 0 (for 23 terms) or 1 (for 22 terms)

The outer-product variety is extremely sparse in F₂^81. Random samples miss the
9D target space completely.

### Result 2: Column Dependency Analysis (rank-23 deletions)
For each of the 23 rank-23 deletions, the 22-column K has D-defect exactly 1.

Removing one more column from K₂₂ typically gives D-defect 2:
- 17/23 deletions: ALL 22 columns essential (every removal → defect 2)
- 6/23 deletions: ONE "free" column (removal keeps defect 1)

### Result 3: Free-Column Search Failure
For the 6 deletions with a free column t:
- K₂₁ (without column t) still has D-defect 1
- Searched ALL 511 nonzero δ ∈ F₂⁹ for B_t ⊕ δ
- ZERO replacements achieve defect 0

This means: the missing D-direction, projected modulo col(K₂₁), does NOT lie
in the 9-dimensional outer-product subspace {a_t ⊗ δ : δ ∈ F₂⁹}.

### Interpretation
The rank-23 scheme's 23 columns barely span the 9D target D. Every column
contributes to D-coverage. After deletion:
- The missing D-direction has a specific F₂^81 representative
- This representative is not achievable by any single outer product from
  the available A-masks
- Even when a column can be freely removed, no replacement from its 
  A-constrained outer-product subspace can cover the gap

This structural obstruction explains:
1. Why the peer's SAT-based Brent completion returns UNSAT for all candidates
2. Why random B search is hopeless (defect always 9)
3. Why single-B modification from rank-23 deletion fails
4. Why Wang-admissible A-multisets don't guarantee Brent completability

### Implications for Rank-22 Existence
The analysis does NOT prove rank ≥ 23, but it reveals the structural barrier:
- 22 outer products from F₂⁹ must jointly span a 9D subspace of F₂^81
- This is a highly constrained covering design problem
- The rank-23 scheme is the only known configuration achieving coverage
- Losing one column destroys coverage with no known repair

### Files
- `deletion_linear_completion.json`: Deletion defect analysis
- `column_dep_all.json`: Column dependency structure
- `K_defect_analysis.py`: Quick structural analysis (shows random B → defect 9)
- `fast_column_dep.py`: Fast column dependency with free-column search

### Next Research Directions
1. **Two-B modification search**: Remove 2 columns, add 2 new outer products
   (computationally expensive: ~262K configs per pair × 231 pairs)
2. **Algebraic characterization**: Characterize which 9D subspaces of F₂^81
   are "reachable" by 22 outer products from prescribed A-subspaces
3. **SAT encoding of B-search**: Equivalent to full Brent SAT (no speedup)
4. **Non-deletion A-multisets**: Different A-multisets might have different 
   column-space geometry, but all tested random starts give defect 9
5. **Constructive approach**: Use the tensor's algebraic symmetry (GL₃×GL₃×S₃)
   to find decompositions with prescribed symmetry properties

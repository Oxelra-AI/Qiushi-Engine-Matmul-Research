# exact semisimple repeated-difference arrangement and block-rank classification

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The rank-22 question was split in analysis into transverse full-span/full-UV-rank charts, lower-UV-rank charts, and the nontransverse termwise-aligned stratum.  The present ARTIFACT attacks the nontransverse termwise-aligned stratum.  analysis already proved the nonsemisimple alignment lemma: in a full-span exact decomposition, termwise alignment with a noncentral stabilizer element forces the three difference operators
\[
D_U(X)=P^TX-XQ^T,\qquad D_V(Y)=Q^TY-YR^T,\qquad D_W(Z)=ZR-PZ
\]
to be semisimple.  Thus the remaining aligned stratum is controlled by diagonal eigenvalue triples
\[
(p_0,p_1,p_2),\quad (q_0,q_1,q_2),\quad (r_0,r_1,r_2).
\]

For every elementary support triple \((a,b,c)\) of the matrix multiplication tensor the three weights are
\[
\alpha_{abc}=p_a-q_b,\qquad \beta_{abc}=q_b-r_c,\qquad \gamma_{abc}=r_c-p_a,
\]
with \(\alpha+\beta+\gamma=0\).  A termwise-aligned rank-one summand must live in one joint weight block; hence an aligned rank-\(r\) decomposition splits block-by-block.  The rank of the whole decomposition is at least the sum of the tensor ranks of the coordinate blocks of \(T_{333}\).

## Exact computation

I implemented exact rational hyperplane-arrangement enumeration in

- [semisimple_arrangement_blockrank.py](../code/semisimple_arrangement_blockrank.py)

and ran

```bash
python3 -u -B scripts/semisimple_arrangement_blockrank.py \
  --out data/semisimple_arrangement/semisimple_arrangement_blockrank.json
```

Output:

- [semisimple_arrangement_blockrank.json](../results/semisimple_arrangement/semisimple_arrangement_blockrank.json)

The script enumerates the intersection lattice of all hyperplanes
\[
(\alpha_{abc},\beta_{abc})=(\alpha_{a'b'c'},\beta_{a'b'c'})
\]
for the 27 elementary products.  Row spaces are represented by exact rational RREFs in the 9 eigenvalue variables \((p,q,r)\), so this is not the analysis small-box enumeration.  It is an exact characteristic-zero equality-pattern enumeration.

Key counts from the run:

```text
exact flats=6425 noncentral=6424 central=1 signatures=58
flattening hist={18: 9, 21: 27, 22: 81, 23: 54, 27: 6253}
certified hist={23: 9, 25: 135, 26: 27, 27: 6253}
min certified=23 excluded=True
elapsed_sec=397.87
```

Detailed JSON fields:

- total flats: 6425;
- central-only flat: 1;
- noncentral flats: 6424;
- distinct noncentral block signatures: 58, exactly matching the 58 signatures seen in analysis's small-box pilot;
- flattening-only block-rank sums: 18, 21, 22, 23, 27;
- after adding the small rectangular matrix-multiplication block lower bounds, certified sums become 23, 25, 26, 27;
- no noncentral signature has certified block-rank sum \(\le22\).

## Block-rank input

The exact enumeration reduces the hard low-flattening cases to only three kinds of known small matrix-multiplication blocks:

1. Flattening-sum 18 patterns: a \(M_{\langle 3,3,2\rangle}\) (or cyclic permutation) block plus a \(M_{\langle3,3,1\rangle}\) block.  Flattening gives \(9+9=18\), but the rectangular block has lower bound \(R(M_{\langle3,3,2\rangle})\ge14\), so the sum is at least \(14+9=23\).
2. Flattening-sum 21 patterns: a \(M_{\langle3,2,2\rangle}\) (or cyclic permutation) block plus three vector/matrix-vector blocks with flattening ranks \(6,6,3\).  The internally checked exterior-flattening lower bound \(R(M_{\langle3,2,2\rangle})\ge8\) already raises the sum to at least \(8+6+6+3=23\).
3. Flattening-sum 22 patterns: a \(M_{\langle2,2,2\rangle}\) block plus six smaller blocks.  The internally checked exterior-flattening lower bound \(R(M_{\langle2,2,2\rangle})\ge6\) already raises the sum to at least \(6+5+4+4+2+2+1=24\) in the worst representatives.

The first script version used an unsupported universal formula.  review correctly flagged that as too strong: if it held for all formats it would conflict with the known history of square matrix-multiplication lower bounds.  I patched the script and reran it as `semisimple_arrangement_blockrank_v3_weaker_inputs.json`, using only a finite table with one real external zero-margin input: \(R(M_{\langle3,3,2\rangle})\ge14\), plus weaker internally checked exterior-flattening bounds for the other low blocks.  The rerun still excludes all noncentral semisimple signatures:

```text
exact flats=6425 noncentral=6424 central=1 signatures=58
flattening hist={18: 9, 21: 27, 22: 81, 23: 54, 27: 6253}
certified hist={23: 36, 24: 108, 25: 27, 27: 6253}
min certified=23 excluded=True
```

For the critical \(M_{\langle3,3,2\rangle}\) number, Landsberg's paper `Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md` gives an inspectable secondary source: lines 33--37 define \(M_{\langle n,n,m\rangle}\) and quote Bläser's bound
\[
R(M_{\langle n,n,m\rangle})\ge 2nm-m+2n-2,
\]
which gives \(2\cdot3\cdot2-2+6-2=14\) for \(M_{\langle3,3,2\rangle}\).  Lines 52 and 155--156 record that Landsberg works over \(\mathbb C\) and cite Bläser's small-format paper.  I attempted DOI/title retrieval of the primary Bläser paper but did not obtain a usable object.  Thus the enumeration is fully checked, and the block input has a local secondary citation; final publication-level use should still inspect/cite Bläser 2003 directly.

I also tested ordinary Koszul/exterior flattenings in

- [koszul_block_bounds.py](../../symmetry_and_residuals/code/koszul_block_bounds.py)
- [koszul_block_bounds.json](../results/semisimple_arrangement/koszul_block_bounds.json)

They give only \(11\) for \(M_{\langle3,3,2\rangle}\), but do give the sufficient weaker bounds \(8\) for \(M_{\langle3,2,2\rangle}\) and \(6\) for \(M_{\langle2,2,2\rangle}\).  Thus the only remaining external small-format theorem needed by this ARTIFACT is Bläser's \(R(M_{\langle3,3,2\rangle})\ge14\).

## Mathematical consequence

Subject to Bläser's quoted small-format input \(R(M_{\langle3,3,2\rangle})\ge14\) over the relevant characteristic-zero field (or over \(\mathbb C\), which suffices after embedding finitely generated characteristic-zero coefficient fields), the full-span semisimple noncentral termwise-aligned stratum contains no rank-22 decomposition of \(T_{333}\).  Combined with the analysis nonsemisimple alignment lemma, this removes the entire full-span termwise-aligned nontransverse stabilizer stratum from the characteristic-zero rank-22 problem.

What remains for characteristic zero is then sharper:

1. transverse full-span/full-UV-rank rank-22 decompositions, where finite moving-frame gauge charts and the projected-kernel equations remain active;
2. lower-UV-rank cases, corresponding to separate projected-kernel models with \(r\le21\);
3. direct primary-source verification or a short self-contained proof note for Bläser's \(R(M_{\langle3,3,2\rangle})\ge14\) input.

This does not prove \(R(T_{333})\ge23\) by itself, because the transverse and lower-UV-rank layers remain open.  It is nevertheless a genuine reduction: the nontransverse semisimple-aligned branch, which analysis showed was the difficult aligned residue after Jordan analysis, is no longer an active source of rank-22 candidates once the cited small-format bounds are accepted.

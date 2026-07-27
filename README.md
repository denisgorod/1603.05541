# The first rational Pontryagin class of a combinatorial manifold

A GAP realization of Gaifullin's algorithm for the first rational Pontryagin
class of a combinatorial manifold, together with the input needed to run it on
the Brehm–Kühnel complex M<sup>8</sup><sub>15</sub>.

This is the program accompanying

> D. Gorodkov. *A 15-Vertex Triangulation of the Quaternionic Projective Plane.*
> Discrete & Computational Geometry **62**(2), 348–373 (2019).
> [doi:10.1007/s00454-018-00055-w](https://doi.org/10.1007/s00454-018-00055-w) ·
> [arXiv:1603.05541](https://arxiv.org/abs/1603.05541)

In 1992 Brehm and Kühnel constructed an 8-dimensional simplicial complex
M<sup>8</sup><sub>15</sub> on 15 vertices and showed it to be a manifold "like a
projective plane" in the sense of Eells and Kuiper. Deciding whether it is
homeomorphic to **HP**<sup>2</sup> reduces to computing its first rational
Pontryagin class. Running this program on M<sup>8</sup><sub>15</sub> gives

> p<sub>1</sub> = 2u, where u is the image of a generator of
> H<sup>4</sup>(M<sup>8</sup><sub>15</sub>, **Z**) ≅ **Z** in
> H<sup>4</sup>(M<sup>8</sup><sub>15</sub>, **Q**),

which with Proposition 4.4 of the article identifies M<sup>8</sup><sub>15</sub>
as PL homeomorphic to **HP**<sup>2</sup>, and hence as a minimal triangulation
of it.

## Requirements

* GAP 4
* the [simpcomp](https://github.com/simpcomp-team/simpcomp) package, used in the
  final step for the homology of the input complex

## Files

| File | |
| --- | --- |
| `Gamma2.g` | The program. Reads the input, runs the main loop over the (n−4)-simplices, and assembles the answer. This is the file to read into GAP. |
| `Decomposition.g` | The method library: bistellar moves, links, orientations, complexity, the values of the cocycle on elementary cycles, and the decomposition of a cycle into a linear combination of them. Read by `Gamma2.g`. |
| `BISTELLAR.g` | Lutz's BISTELLAR (version Nov/2003) with the instrumentation `Gamma2.g` consumes: the facet list after every flip is recorded in `bisfaces`, and the move itself in `randomelements`. |
| `Pontryagin-M_8_15.testobject` | M<sup>8</sup><sub>15</sub> — 490 facets on 15 vertices — together with the precomputed BISTELLAR output for each of its 3003 4-simplices. |
| `BISTELLAR.testobject`, `BISTELLAR.log`, `BISTELLAR.out` | A sample BISTELLAR run: a 15-vertex 3-sphere on 90 facets reduced in 77 rounds to the boundary of the 4-simplex. Regenerated on every run, and the strategy is randomised, so the round count varies. |

## Running

```
gap> Read("Gamma2.g");
```

The input is selected at the top of `Gamma2.g`:

* `object := 1` — M<sup>8</sup><sub>15</sub>, from `Pontryagin-M_8_15.testobject`.
  That file already carries the BISTELLAR output for every 4-simplex, so the
  flip sequences are not recomputed and `BISTELLAR.g` is not read.
* `object := 0` — an arbitrary pure simplicial complex, given as
  `Pfacets := [...];;` in `Pontryagin.testobject`. Each link is written to
  `BISTELLAR.testobject` and passed to `BISTELLAR.g` as it is reached.

Output goes to the screen and to `Pontryagin.log`. The final line is

```
p1 coefficient = <c>
```

meaning the first Pontryagin class is `c` times the image of a generator of
H<sup>4</sup>(K, **Z**) in H<sup>4</sup>(K, **Q**). The sign depends on which of
the two generators simpcomp returns. For M<sup>8</sup><sub>15</sub> the
coefficient has magnitude 2.

The last step is written for the case H<sup>4</sup> = **Z** and is easily
rewritten in general.

## The algorithm

A local formula for the first Pontryagin class assigns a rational number to the
isomorphism class of the link of each (n−4)-simplex. Gaifullin's formula
expresses that number through a cocycle on the graph Γ<sub>2</sub>, whose
vertices are oriented combinatorial 2-spheres and whose edges are bistellar
moves between them; the cocycle is prescribed on a set of *elementary cycles*
that generate the cycle space (§5.2 of the article). Evaluating it therefore
needs every cycle to be written as a linear combination of elementary ones.

`Gamma2.g` follows the realization in §6:

1. For each (n−4)-simplex σ, find a sequence ξ<sub>σ</sub> of bistellar moves
   taking link σ to the boundary of a simplex — this is what BISTELLAR does,
   descending by gradually reducing the number of vertices.
2. For each vertex v of link σ, including vertices created along ξ<sub>σ</sub>,
   induce ξ<sub>σ</sub> on link<sub>link σ</sub>(v). Each of those is a
   combinatorial 2-sphere, so the induced sequence ξ<sub>σ,v</sub> is a chain in
   Γ<sub>2</sub>.
3. Close ξ<sub>σ,v</sub> into a cycle η<sub>σ,v</sub>, using a canonical chain
   back to ∂Δ³ and a chain joining differently labelled copies of ∂Δ³.
4. Decompose η<sub>σ,v</sub> into a linear combination of elementary cycles and
   sum the cocycle over them; adding up over v gives f(⟨link σ⟩).
5. Form the chain f<sub>♯</sub>(K) = Σ f(⟨link σ⟩)·σ, which represents the
   homology class dual to the first Pontryagin class, and express it through the
   boundaries of the (n−3)-faces and a generator of H<sub>n−4</sub>.

Steps 1–3 are the main loop of `Gamma2.g`; step 4 is `decomposition` in
`Decomposition.g`; step 5 is the tail of `Gamma2.g`, using simpcomp.

### Decomposition into elementary cycles

The decomposition (§5.3) is an induction on complexity. For a combinatorial
2-sphere L with k vertices,

* a(L) = k, if L has a vertex of degree 3;
* a(L) = k + 1/3, if L has a vertex of degree 4 but none of degree 3;
* a(L) = k + 2/3, otherwise,

and for a bistellar move β : L₁ → L₂,

* a(β) = max(a(L₁), a(L₂)), if a(L₁) ≠ a(L₂);
* a(β) = a(L₁) + 1/6, if a(L₁) = a(L₂).

Writing a = k + b/6, the induction step is proved separately for each
b = 0, …, 5, and `decomposition` branches the same way. In the code
`difficulty_tri` is 3·a(L) and `difficulty_bis` is 6·a(β), so
`difficulty_bis mod 6` is exactly b, with 0 read as 6. For odd b the moves of
greatest complexity join spheres of equal complexity and are treated one at a
time; for even b they come in pairs L₁ ← L → L₂ through a sphere L of greater
complexity, and each pair is replaced by a chain that routes around L.

Each round `decomposition` locates the positions of greatest complexity in the
chain, rewrites it there, and returns the value the removed elementary cycles
contribute. A configuration matching no case of a branch is recorded in the
global `unhandled_cases` — the three consecutive spheres, the orientation, the
two U-sets and the vertex degrees — and reported.

## Citation

If you use this program, please cite

> D. Gorodkov. *A 15-Vertex Triangulation of the Quaternionic Projective Plane.*
> Discrete & Computational Geometry **62**(2), 348–373 (2019).

The algorithm realized here is due to Gaifullin:

> A. A. Gaifullin. *Local formulae for combinatorial Pontryagin classes.*
> Izv. Math. **68**(5), 861–910 (2004).
>
> A. A. Gaifullin. *Configuration spaces, bistellar moves, and combinatorial
> formulae for the first Pontryagin class.* Proc. Steklov Inst. Math. **268**,
> 70–86 (2010).

The complex M<sup>8</sup><sub>15</sub> is due to Brehm and Kühnel:

> U. Brehm, W. Kühnel. *15-Vertex triangulations of 8-manifolds.*
> Math. Ann. **294**, 167–193 (1992).

The computation uses GAP and the simpcomp package:

> The GAP Group. *GAP — Groups, Algorithms, and Programming.*
> <https://www.gap-system.org>
>
> F. Effenberger, J. Spreer. *simpcomp — a GAP toolkit for simplicial complexes.*

## Attribution and licensing

Copyright © 2019, 2026 Denis Gorodkov.

The code written for this project — `Gamma2.g`, `Decomposition.g` and the input
files — is released under the GNU General Public License v3; see `LICENSE`, and
the notice at the head of each source file.

`BISTELLAR.g` is not part of that: it is Frank H. Lutz's program BISTELLAR
(version Nov/2003; the first version, Nov/1997, is by Anders Björner and
Frank H. Lutz), distributed from

> <http://www.math.tu-berlin.de/diskregeom/stellar/>

and described in

> A. Björner, F. H. Lutz. *Simplicial manifolds, bistellar flips and a 16-vertex
> triangulation of the Poincaré homology 3-sphere.* Exp. Math. **9**(2),
> 275–289 (2000).

The copy included here differs from the original only by the additions marked
with `##` fences, which record the facet list after each flip in `bisfaces` and
the move itself in `randomelements`; the file carries a note to that effect at
its head. It is reproduced with attribution to its authors, and is not covered
by this repository's `LICENSE`.

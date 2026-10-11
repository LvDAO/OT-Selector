# OT Selector

This repository gives an affirmative answer to the empirical optimal transport
selection problem stated in **Section 7, Problem 4** of
[*Distributional Limit Theory for Optimal Transport*](https://arxiv.org/html/2505.19104v1#S7)
by Eustasio del Barrio, Alberto González-Sanz, Jean-Michel Loubes, and David
Rodríguez-Vítores. It contains the [TeX article](main.tex), *Deterministic
Selection in Empirical Wasserstein-One Matching*, and its [Lean 4
formalization](OTSelector/Main.lean).

## Main theorem

Let $X_1,\ldots,X_n$ and $Y_1,\ldots,Y_n$ be two independent i.i.d. samples
from the uniform distributions on $[0,1]^2$ and $[2,3]\times[0,1]$,
respectively. Choose a permutation $\sigma_n$ minimizing total Euclidean
distance, with a fixed ordering to resolve ties, and define the empirical
transport plan by

$$
\sigma_n\in\operatorname*{arg\,min}_{\sigma}
\sum_{i=1}^n\lVert X_i-Y_{\sigma(i)}\rVert_2,
\qquad
\pi_n=\frac1n\sum_{i=1}^n\delta_{(X_i,Y_{\sigma_n(i)})}.
$$

**There exists a deterministic coupling $\kappa_\infty$ of two uniform
$[0,1]$ distributions such that**

$$
\pi_n\xrightarrow{\mathbb P}
\operatorname{Law}\bigl((U,T),(2+V,T)\bigr)
\quad\text{in the weak topology},
$$

where $(U,V)\sim\kappa_\infty$ and $T\sim\operatorname{Unif}[0,1]$ are
independent. Thus independent sampling selects a single deterministic
optimal plan. This plan preserves height and has the same joint distribution
of paired horizontal coordinates at every height.

The proof identifies $\kappa_\infty$ through the source-Palm distribution of
a unique stationary local matching. The main formal theorem is
[`OTSelector.main_selector`](OTSelector/Main.lean).

## Verify the Lean proof

Install [Lean via elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/LvDAO/OT-Selector.git
cd OT-Selector
lake exe cache get
lake build
lake env lean Verify.lean
```

The Lean version is fixed by [`lean-toolchain`](lean-toolchain), and dependency
versions are fixed by [`lakefile.toml`](lakefile.toml) and
[`lake-manifest.json`](lake-manifest.json). The required LeanPool sources are
included under [`vendor/lean-pool`](vendor/lean-pool).

[`Verify.lean`](Verify.lean) checks the transitive axiom dependencies of the
project and vendored LeanPool declarations against `propext`,
`Classical.choice`, and `Quot.sound`.

## Build and download the paper

With TeX Live and `latexmk` installed, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

This produces `main.pdf` in the repository root.

The [Build PDF workflow](https://github.com/LvDAO/OT-Selector/actions/workflows/build-pdf.yml)
automatically compiles the paper on pushes to `main` and on pull requests.
It can also be started manually with **Run workflow**. Open a successful run
and download **OT-Selector-paper** from its **Artifacts** section to get
`main.pdf`.

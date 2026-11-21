# Erdős Problem 770(iii)

Lean 4 formalization of the arithmetic reduction in Dillon MacKenzie's preprint [*The large-prime threshold in Erdős Problem 770(iii)*](https://doi.org/10.5281/zenodo.24409350).

The main theorem, `Erdos770Reduction.threshold`, is in [Erdos770.lean](Erdos770.lean). It shows that the largest prime `p` with `p - 1 ∣ n` is the first cutoff where the collective gcd is one, given the Fermat congruence, the existence of small primitive roots, enough distinct products of small primes, and the root bound over a prime field. These inputs are explicit hypotheses in Lean. The preprint gives the argument from Dirichlet GRH to the eventual threshold.

## Check the formalization

With [Elan](https://github.com/leanprover/elan) installed, run this from the repository root. The toolchain file pins Lean 4.19.0. The proof uses Lean's bundled libraries.

```sh
lean Erdos770.lean
```

The file prints the theorem's axiom dependencies.

```text
'Erdos770Reduction.threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
```

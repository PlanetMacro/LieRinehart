import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie–Rinehart algebras

This file defines **Lie–Rinehart algebras** following the classical formulation:

* `A` is a commutative `R`‑algebra;
* `L` is an `A`‑module equipped with an `R`‑Lie algebra structure;
* there is an `A`‑linear *anchor* map `ρ : L →ₗ[A] Derivation R A A` sending each element of `L`
  to an `R`‑linear derivation of `A`;
* the anchor is a Lie algebra morphism; and
* the Lie bracket and module structure satisfy the Leibniz rule
  `⁅x, a • y⁆ = a • ⁅x, y⁆ + (ρ x) a • y`.

"JOHANNES HUEBSCHMANN, Lie-Rinehart algebras, Gerstenhaber algebras
 and Batalin-Vilkovisky algebras,
 Annales de l’institut Fourier, to me 48, no 2 (1998), p. 425-440
-/

structure LieRinehart
  (R : Type*) [CommRing R] -- `R` is a commutative ring with `1`
  (A : Type*) [CommRing A] [Algebra R A] -- `A` is a commutative `R`-algebra
  (L : Type*) [LieRing L] [LieAlgebra R L] -- `L` is a `R` Lie-algebra
              [Module A L] -- `L` is an `A`-module
    where
    ρ : L →ₗ[A] Derivation R A A -- The anchor map `ρ : L → Der_R(A)` is `A`‑linear.
    anchor_lie : ∀ x y : L, ρ ⁅x, y⁆ = ⁅ρ x, ρ y⁆ -- anchor is a morphism of Lie algebras.
    leibniz : ∀ (x y : L) (a : A), ⁅x, a • y⁆ = a • ⁅x, y⁆ + (ρ x) a • y -- Leibnitz rule

attribute [simp] LieRinehart.leibniz

namespace LieRinehart

variable
  (R : Type*) [CommRing R]
  (A : Type*) [CommRing A] [Algebra R A]
  (L : Type*) [LieRing L] [LieAlgebra R L] [Module A L]

end LieRinehart

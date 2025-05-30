import Mathlib.RingTheory.Derivation.Basic
import LieRinehart.LieRinehartAlgebra
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.Manifold.IsManifold.Basic


open LieRinehart
open Topology
open TopologicalSpace
open scoped Manifold ContDiff
/-!
Example Lie–Rinehart algebra of a smooth manifold M:

R = ℝ
A = C^∞(M) = C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
L = Derivation ℝ A A (algebraic derivations = vector fields)
anchor = id : L →ₗ[A] Derivation ℝ A A
-/

noncomputable def ManifoldExample {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M] :
  LieRinehart
    ℝ
    (C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (Derivation ℝ (C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)) :=
{  ρ := LinearMap.id,
   anchor_lie := by
    /- Goal: ∀ (x y : Derivation ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯),
  LinearMap.id ⁅x, y⁆ = ⁅LinearMap.id x, LinearMap.id y⁆ -/
    -- We need a theorem, that the identity map on derivations commutates with the
    -- Lie bracket
   ,
   leibniz := by sorry -- WE KEEP THIS FOR NOW AS SORRY; FOCUSSING ON THE FIRST}

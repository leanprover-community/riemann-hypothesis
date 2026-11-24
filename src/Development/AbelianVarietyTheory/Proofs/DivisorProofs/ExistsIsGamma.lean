module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

namespace FrobTwist

def Tw (K V : Type) [CommRing K] [AddCommGroup V] [Module K V] : Type := ExteriorAlgebra K V

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

instance : Ring (Tw K V) := inferInstanceAs (Ring (ExteriorAlgebra K V))

abbrev twAlg (p : ℕ) [Fact p.Prime] [CharP K p] : Algebra K (Tw K V) :=
  RingHom.toAlgebra' ((algebraMap K (ExteriorAlgebra K V)).comp (frobenius K p))
    (fun c x => Algebra.commutes (R := K) (A := ExteriorAlgebra K V) _ x)

end FrobTwist


open FrobTwist in
theorem exists_isGamma {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (f : V →+ V) (hf : ∀ (c : K) v, f (c • v) = c ^ p • f v) :
    ∃ γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V, IsGamma p f γ := by
  letI : Algebra K (Tw K V) := twAlg p
  let g : V →ₗ[K] Tw K V :=
    { toFun := fun v => (ExteriorAlgebra.ι K (f v) : ExteriorAlgebra K V)
      map_add' := fun v w => by
        show ExteriorAlgebra.ι K (f (v + w)) = ExteriorAlgebra.ι K (f v) + ExteriorAlgebra.ι K (f w)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        have h1 : ExteriorAlgebra.ι K (f (c • v)) =
            algebraMap K (ExteriorAlgebra K V) (c ^ p) * ExteriorAlgebra.ι K (f v) := by
          rw [hf, map_smul, Algebra.smul_def]
        exact h1 }
  have hg : ∀ v, g v * g v = 0 := fun v => ExteriorAlgebra.ι_sq_zero (R := K) (f v)
  let Γ : ExteriorAlgebra K V →ₐ[K] Tw K V := ExteriorAlgebra.lift K ⟨g, hg⟩
  refine ⟨(Γ.toRingHom : ExteriorAlgebra K V →+* ExteriorAlgebra K V), ?_, ?_⟩
  · intro c
    have := Γ.commutes c
    exact this
  · intro v
    have := ExteriorAlgebra.lift_ι_apply K (A := Tw K V) g hg v
    exact this

end GlobalTheory.DI

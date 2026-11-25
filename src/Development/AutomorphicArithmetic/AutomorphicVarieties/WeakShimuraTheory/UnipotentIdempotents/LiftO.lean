module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.liftO :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* (PadicAlgCl l)ˣ), Continuous χ → (∀ g, (χ g : PadicAlgCl l) ∈ c.O) → ∃ χ' : Γ →* c.Oˣ, toQ χ' = χ ∧ (AdicCont (maximalIdeal c.O) fun g => (χ' g : c.O)) ∧ ∀ g, ‖(χ g : PadicAlgCl l) - 1‖ < 1 → residue c.O (χ' g) = 1 := by
  intro l _ c Γ _ _ χ hχ hO
  have hinv : ∀ g, (χ g : PadicAlgCl l) * (χ g⁻¹ : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hinv' : ∀ g, (χ g⁻¹ : PadicAlgCl l) * (χ g : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  let u : Γ → c.Oˣ := fun g =>
    ⟨⟨χ g, hO g⟩, ⟨χ g⁻¹, hO g⁻¹⟩, Subtype.ext (hinv g), Subtype.ext (hinv' g)⟩
  let χ' : Γ →* c.Oˣ :=
    { toFun := u
      map_one' := by
        ext
        simp [u]
      map_mul' := by
        intro a b
        ext
        simp [u] }
  have hval : ∀ g, ((χ' g : c.O) : PadicAlgCl l) = χ g := fun g => rfl
  refine ⟨χ', ?_, ?_, ?_⟩
  · ext g
    rfl
  · rw [(X.So.adicCont l c).2 Γ]
    exact Continuous.subtype_mk (Units.continuous_val.comp hχ) _
  · intro g hg
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub, residue_eq_zero_iff,
      (Fr.sc_norm l c _).2]
    simpa [hval] using hg

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_padicInt_lift_of_integralAt :
    ∀ {Γ : Type} [CommGroup Γ] [Finite Γ] (l : ℕ) [Fact l.Prime] (y : MonoidAlgebra ℚ Γ), IntAt l 0 y → ∃ Yp : MonoidAlgebra ℤ_[l] Γ, MonoidAlgebra.mapRingHom Γ (algebraMap ℤ_[l] ℚ_[l]) Yp = MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) y := by
  intro Γ _ _ l _ y hy
  have hle : ∀ g : Γ, ‖((y.coeff g : ℚ) : ℚ_[l])‖ ≤ 1 := by
    intro g
    have h := hy g
    rw [pow_zero, div_one, mem_Zl] at h
    exact Padic.norm_rat_le_one h
  let x : Γ → ℤ_[l] := fun g => ⟨((y.coeff g : ℚ) : ℚ_[l]), hle g⟩
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]
  change algebraMap ℤ_[l] ℚ_[l] ((Finsupp.equivFunOnFinite.symm x) g) = _
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  rfl

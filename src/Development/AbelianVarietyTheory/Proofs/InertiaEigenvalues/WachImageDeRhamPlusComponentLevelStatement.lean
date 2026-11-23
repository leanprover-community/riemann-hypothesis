module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevel
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

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wach_image_deRham_plus_component_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → ∃ Ψ : ↥(W.N T) → T.V ⊗[ℚ_[l]] (D.loc l).R.BdR, (∀ x, Ψ x ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0) ∧ (∀ z ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → (D.loc l).R.BdR) (x : Fin m → ↥(W.N T)), (∀ j, b j ∈ ((D.loc l).PD K).Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧ ∀ (x : ↥(W.N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex C h T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS (D.loc l) s ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (tS (D.loc l) s ^ r) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T i ζ x ((r : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.NL.PerS.image | exact GlobalTheory.NL.PerS.image | (intros; apply GlobalTheory.NL.PerS.image <;> assumption)

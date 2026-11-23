module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponent
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]  (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 → ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR) (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR), mulVR T (tS ^ w) z - ∑ j, mulVR T (b j) (D j) ∈ compKer T ι → (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈ PD.Fil (m : ℤ)) → (∀ k : ℤ, L k - ∑ j, cz (e j) (k + (w : ℤ)) • D j ∈ compKer T ι) → ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS ^ a) (mulVR T pk z) - mulVR T pk (∑ k ∈ Finset.range M, mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.HWL.Cmp.filt_expansion_component | exact GlobalTheory.HWL.Cmp.filt_expansion_component | (intros; apply GlobalTheory.HWL.Cmp.filt_expansion_component <;> assumption)

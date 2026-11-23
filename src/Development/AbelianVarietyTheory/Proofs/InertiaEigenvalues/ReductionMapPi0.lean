module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem map_pi0 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [Algebra O k] [CharP k l], PD.p = l → ∀ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, (∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)) → PowerSeries.map (algebraMap O k) W.π₀₁ = 1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1}, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l _ k _ _ _ hp e he

  have hsub : ∀ z : ℤ_[l], GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z (1 + PowerSeries.X) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z := by
    intro z
    have ha : PowerSeries.HasSubst (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z - 1) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.binomialSeries_constantCoeff, map_one, sub_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi
    rw [← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, PowerSeries.substAlgHom_X ha]
    ring

  have hl : (l : k⟦X⟧) = 0 := by
    rw [← map_natCast (PowerSeries.C : k →+* k⟦X⟧), CharP.cast_eq_zero, map_zero]
  unfold LocWach.π₀₁

  rw [map_add (f := _), map_sub, map_one, map_natCast, hp, hl, sub_zero, map_sum, ← Finset.sum_coe_sort W.DelF,
  Finset.sum_congr rfl fun δ _ => by rw [he, map_add (f := _), map_one, PowerSeries.map_X, hsub],
  ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]

end GlobalTheory.RedFun

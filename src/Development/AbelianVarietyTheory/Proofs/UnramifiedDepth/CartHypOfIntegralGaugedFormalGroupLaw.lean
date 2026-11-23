module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPureTypicalCurveWithIntegralTangentStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSetStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNeStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ShiftedSumMemTypicalCurveSetStatement
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
import Formalism.LocalToGlobal.CharacterGerms.ValNonnegLeadingCoeffOfMemTySet
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
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem cartHyp_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → (∀ g, HasTeich X V g) → ∀ g, X.CartHyp V g := by
  intro C _ V d _ I _ κ _ X hL hP hT g
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hL.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hh := hL.axes 0
  refine
    { zero := X.zero_mem hlg0 hh V g
      add := X.add_mem V g (GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hL) hL.uint
      neg := X.neg_mem V g hL.odd
      teich := X.teich_mem V g
      Vm := X.V_mem V g
      Fm := GlobalTheory.T.frobenius_mem_typicalCurveSet C V d I κ X hL g
      sumV := GlobalTheory.T.shiftedSum_mem_typicalCurveSet C V d I κ X hL g
      t2 := X.val_nonneg_leading_coeff_of_mem_tySet V g hL.lin hh ?_ (GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne C V d I κ X hL g (hT g))
      t3 := X.const_mem_type_set_of_nonneg hlg0 hh V g
      t4 := GlobalTheory.T.exists_pure_typical_curve_with_integral_tangent C V d I κ X hL hP g (hT g) }
  obtain ⟨w, hw, huw⟩ := hL.sat g
  refine ⟨w, hw, fun c c' => ?_⟩
  split_ifs with h
  · exact (huw c c').1 h
  · exact (huw c c').2 h

end GlobalTheory.RowLaw

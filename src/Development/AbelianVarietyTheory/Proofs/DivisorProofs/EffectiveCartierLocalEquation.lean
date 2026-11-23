module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.IdealDiv

theorem unitAt_div_of_ideal_eq {Y : Scheme.{0}} [IsIntegral Y] (J : Y.IdealSheafData) {y : Y}
    {U V : Y.affineOpens} {f : Γ(Y, U.1)} {f' : Γ(Y, V.1)} (hU : y ∈ U.1) (hV : y ∈ V.1)
    (hf : J.ideal U = Ideal.span {f}) (hf' : J.ideal V = Ideal.span {f'})
    (h0 : fnOf U.1 (gen_mem hU) f ≠ 0) :
    UnitAt y (fnOf V.1 (gen_mem hV) f' / fnOf U.1 (gen_mem hU) f) := by
  obtain ⟨h, hhW, hxh⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨_, ⟨hU, hV⟩⟩ hU
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, U.2.basicOpen h⟩
  have hWU : Wa.1 ≤ U.1 := hhW.trans inf_le_left
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_right
  haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩
  have e1 : J.ideal Wa = Ideal.span {resG Y hWU f} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := U) hWU, hf, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : J.ideal Wa = Ideal.span {resG Y hWV f'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, hf', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (e1.symm.trans e2)
  have hg := gen_mem (U := Wa.1) hxh
  have e := congrArg (fnOf Wa.1 hg) hu
  rw [map_mul, fnOf_resG, fnOf_resG] at e
  rw [← e, mul_div_cancel_left₀ _ h0]
  exact unitAt_fnOf hxh hg u

theorem exists_cartierDiv_of_effCartier : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData),
    FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧
      ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0),
        J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  intro Y _ J hJ
  choose U f hyU hnzd hid using hJ
  have hne : ∀ y, fnOf (U y).1 (gen_mem (hyU y)) (f y) ≠ 0 := by
    intro y h
    haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    have h0 : f y = 0 := fnOf_injective _ _ (h.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero (hnzd y) h0
  let v : ∀ y : Y, Y.functionFieldˣ := fun y => Units.mk0 _ (hne y)
  let E : CartierDiv Y := show cartierGroup Y from ⟨fun y => germOf y (v y), fun x =>
    ⟨(U x).1, hyU x, v x, fun y hy =>
      germOf_eq_iff.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) (hid x) (hne y))⟩⟩
  have hE : ∀ y, E.IsEqn y (v y) := fun y => rfl
  refine ⟨E, fun x => ⟨v x, hE x, by rw [one_mul]; exact regAt_fnOf (hyU x) _ _⟩, ?_, ?_⟩
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, (hE x).mem_supp_iff, Units.val_mk0, unitAt_fnOf_iff (hyU x),
      Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hyU x), hid x, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  · intro y V g hy hg hV
    exact (hE y).iff_unitAt.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) hV (hne y))

end GlobalTheory.Cartier.IdealDiv

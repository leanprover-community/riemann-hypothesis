module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.ord_fnPull_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  intro k _ X Y _ _ p s _ hs E' E h g
  let φ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring fun a => (h _).1 a.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hs.1 (congrArg Subtype.val e)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hs.2 (b : Y.functionField)
    exact ⟨⟨a, (h a).2 (ha ▸ b.2)⟩, Subtype.ext ha⟩
  let e : E.ring ≃+* E'.ring := RingEquiv.ofBijective φ hφ
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, u, eg⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := Y.functionField) (ht.map e)
    (Units.map e.toMonoidHom u) m
  rw [← eg, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have eg' : ((fnPull s g : Y.functionFieldˣ) : Y.functionField) =
      algebraMap E'.ring Y.functionField (Units.map e.toMonoidHom u : E'.ringˣ) *
        algebraMap E'.ring Y.functionField (e t) ^ m := by
    change functionFieldMap s (g : X.functionField) = _
    rw [eg, map_mul, map_zpow₀]
    rfl
  rw [← eg', ordTop_vw_of_ne_zero _ (fnPull s g).ne_zero, WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.Discrepancy

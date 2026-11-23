module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLocalMembership
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isMultIdeal_iff_regularAt : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro k _ _ X _ p n hproj η m G Y _ _ s _ K B F hη hm hres hF J
  have key := inMultAt_iff_regularAt_logRes k X p n hproj η m G Y s K B F hη hm hres hF
  unfold IsMultIdeal
  refine forall_congr' fun U => forall_congr' fun f => iff_congr Iff.rfl ?_
  constructor
  · intro H y hy
    by_cases h0 : fnOf U.1 (gen_mem hy) f = 0
    · rw [h0, map_zero]
      obtain ⟨g, hg⟩ := (-F).exists_isEqn y
      refine ⟨g, hg, ?_⟩
      rw [zero_mul]
      exact (regAt_zero (X := Y) (x := y))
    · have := (key (s y) (Units.mk0 _ h0)).1 (H (s y) hy _ rfl) y rfl
      simpa using this
  · intro H x hx u hu
    rw [key]
    rintro y rfl
    rw [hu]
    exact H y hx

end GlobalTheory.Discrepancy

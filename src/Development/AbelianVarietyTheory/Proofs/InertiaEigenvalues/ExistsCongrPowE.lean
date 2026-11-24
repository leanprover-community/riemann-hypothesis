module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WApprox

theorem ρ₀_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by simp only [neg_neg_iff_pos]; positivity)

theorem exists_congr_pow_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ) (x : bk.DS bk.ρ₀),
    ∃ (k : ℕ) (s : bk.S), toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣
      (l : bk.DS bk.ρ₀) ^ k * x - toDisc l (X : bk.S) bk.ρ₀ s := by
  intro l _ K bk m
  induction m with
  | zero => intro x; exact ⟨0, 0, by simp⟩
  | succ m ih =>
    intro x
    obtain ⟨q, k, r, -, hx⟩ := WDiv.weierstrass_div l K bk bk.ρ₀ le_rfl (ρ₀_lt_one bk) x
    obtain ⟨k', s', w, hw⟩ := ih q
    refine ⟨k + k', bk.E * s' + (l : bk.S) ^ k' * (r : bk.S), w, ?_⟩
    have hq : (l : bk.DS bk.ρ₀) ^ k' * q = toDisc l (X : bk.S) bk.ρ₀ s' +
        toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m * w := by rw [← hw]; ring
    calc (l : bk.DS bk.ρ₀) ^ (k + k') * x - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S))
        = (l : bk.DS bk.ρ₀) ^ k' * ((l : bk.DS bk.ρ₀) ^ k * x) - toDisc l (X : bk.S) bk.ρ₀ (bk.E * s' + (l : bk.S) ^ k' * (r : bk.S)) := by ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E * ((l : bk.DS bk.ρ₀) ^ k' * q) - toDisc l (X : bk.S) bk.ρ₀ bk.E * toDisc l (X : bk.S) bk.ρ₀ s' := by
          rw [hx, map_add (f := _), map_mul, map_mul, map_pow, map_natCast]; ring
      _ = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (m + 1) * w := by rw [hq]; ring

end GlobalTheory.BKLim.WApprox

module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime]

theorem acris_zero_surjective : Function.Surjective (PAlg.base l).cris0 := by
  rintro ⟨y, hy⟩
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have hx : xi0 l ∈ RingHom.ker (theta0 l) := by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _
    refine ⟨⟨dpw k (xi0 l), ACris.dpow_mem hx k⟩, Subtype.ext ?_⟩
    show awayW (RingHom.id (Ob l)) (dpw k (xi0 l)) = _
    rw [awayW_id, RingHom.id_apply, dpw]
    show _ = Ring.inverse _ * algebraMap _ _ (WittVector.map (RingHom.id (Ob l)) (xi0 l)) ^ k
    rw [wmap_id]
    rfl
  | algebraMap r =>
    refine ⟨algebraMap (Ainf l) (Acris0 l) r, Subtype.ext ?_⟩
    show awayW (RingHom.id (Ob l)) (algebraMap (Ainf l) (WL l (Ob l)) r) = _
    rw [awayW_id, RingHom.id_apply]
    rfl
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a + b, ?_⟩
    change (PAlg.base l).cris0 (a + b) = (⟨x, hx⟩ : (PAlg.base l).Acr0) + ⟨y, hy⟩
    exact ((PAlg.base l).cris0.map_add a b).trans (congrArg₂ (· + ·) ha hb)
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, by rw [map_mul (PAlg.base l).cris0, ha, hb]; rfl⟩

theorem acris_level_surjective (n : ℕ) : Function.Surjective ((PAlg.base l).cris n) := by
  intro w
  obtain ⟨y, rfl⟩ := (PAlg.base l).mkAcr_surjective n w
  obtain ⟨z, rfl⟩ := acris_zero_surjective (l := l) y
  exact ⟨AdicCompletion.of _ _ z, (PAlg.base l).cris_of n z⟩

end CrystallineSemistableComparison.Pb.Kap

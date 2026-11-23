module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemROf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG2

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_low {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, a < b → lmat Z p g l ρ a b = 0) ∧ ∀ a, lmat Z p g l ρ a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hl0 a b h, hρ0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem corner_fix {L R C : Formalism.L2.SG.LsDatumB.MatP D p} (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1)
    (hC : ∀ a b, ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) → C a b = 0) : L * C * R = C := by
  have hLl : ∀ a, L a (Fin.last D.R.rS) = if a = Fin.last D.R.rS then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h; exact hL1 _
    · exact hL0 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hRl : ∀ b, R (Fin.last D.R.rS) b = if b = Fin.last D.R.rS then 1 else 0 := by
    intro b
    split_ifs with h
    · subst h; exact hR1 _
    · exact hR0 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last D.R.rS) (fun d _ hd => by
      rw [Finset.sum_eq_zero (fun c _ => by rw [hC c d (fun h => hd h.2), mul_zero]), zero_mul]) (by simp),
    Finset.sum_eq_single (Fin.last D.R.rS) (fun c _ hc => by rw [hC c _ (fun h => hc h.1), mul_zero]) (by simp),
    hLl a, hRl b]
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS
  · subst ha; subst hb; simp
  · rw [if_neg hb, mul_zero, hC a b (fun h => hb h.2)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]

end ModeG2

end Formalism.L2.SG.Pf.FibQ

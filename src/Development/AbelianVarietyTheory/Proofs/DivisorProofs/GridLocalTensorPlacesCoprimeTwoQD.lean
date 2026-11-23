module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Formalism.LocalRingCardinality.HostCls
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end

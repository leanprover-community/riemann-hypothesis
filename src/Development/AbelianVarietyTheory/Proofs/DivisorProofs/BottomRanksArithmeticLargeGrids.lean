module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end

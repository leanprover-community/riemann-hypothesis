module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G

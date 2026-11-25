module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilSignShift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianParamOppositeSignEntriesDistGeGap
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ArchRec
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes GlobalTheory.Chain.ParOfNodeGap

namespace GlobalTheory.ArchRec.ParChain

theorem num_bound_two {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 1 ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : 8 * (m : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by gcongr
      _ ≤ (m : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_natCast _ _
  have h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem stepGap_of_gap {D : D7} (h : NodeGap D) (k : Fin D.R.m) : StepGap D k := by
  intro τ
  obtain ⟨N, hN, hgap⟩ := h
  set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh
  have hg : ∀ (i : ℕ) (h : i + 1 < D.R.m),
      h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
    intro i h
    have := hgap τ ⟨i, by omega⟩ h
    rw [hh]
    exact_mod_cast this
  have hS : NcGapGe (lamS D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hT : NcGapGe (lamT D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N := fun j hj => by
    have := Nat.mul_le_mul_right D.R.t hj
    unfold Ranks.rankX' at hN
    unfold Ranks.rankY
    omega
  have h3 : 8 * D.R.m ≤ N := by
    have h8 : 8 ≤ D.R.t := by
      have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have := Nat.mul_le_mul_left D.R.m h8
    unfold Ranks.rankX' at hN
    omega
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀ := by
    have h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr _ k.2
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have h2 := num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3
  exact ⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs),
    fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩

theorem parChain : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  intro D k τ
  obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
  refine ⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩
  have h := stepGap_of_gap hG k τ
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  rw [hr] at h
  refine (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_
  rwa [← h1, ← h2]

end GlobalTheory.ArchRec.ParChain

end

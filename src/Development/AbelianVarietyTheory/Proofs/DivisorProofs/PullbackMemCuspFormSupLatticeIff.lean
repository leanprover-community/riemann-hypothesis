module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
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

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.PullLat

variable {D : D7}

theorem levPull_of_pull {T : Core D} {j : ℕ} (Y : Deep T j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) {g : Rul Y.d.Xo₂ Y.d.c₂} (hp : Y.Pull f g) :
    GlobalTheory.LevPull.Pull Y.d (GlobalTheory.FieldBC.rulBC Y.hle f) g := by
  intro k _ _ _ _ hk y₂ y hov
  letI : Algebra T.Q.c.F k := GlobalTheory.FieldBC.resAlg Y.hle k
  have ho : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
  rw [((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ Y.hle).1 a n f hf).2 k ho y]
  exact hp k ho hk y₂ y (y.res Y.hle ho) hov rfl rfl HEq.rfl

theorem pull_mem_latW : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j →
    Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))
      (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  intro D T j Y e o hT hj hY a n f g hp
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hfs : (f : T.R j) ∈ sec (T.Q.Xo j) T.Q.c a n := by
    have h : (f : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) a n := by rw [← cuspW_wtZ]; exact f.2
    exact cusp_le_sec _ _ _ _ _ h
  have hgs : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have h : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by rw [← cuspW_wtZ]; exact g.2
    exact cusp_le_sec _ _ _ _ _ h
  have hfs' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) _ _ Y.hle).1 a n _ hfs).1
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have h1 := GlobalTheory.CoverInt.pull_intAt_iff _ _ _ _ _ _ Y.d hpos hY.lev.1 (Or.inl ⟨hne, hL.levA⟩) a n _ hfs' _ hgs (levPull_of_pull Y hfs hp)
  have h2 := GlobalTheory.T.isIntegralRule_ruleBaseChangeCoeffField_iff _ _ _ _ _ _ _ Y.hle a n _ hfs
  exact h1.trans h2

end GlobalTheory.CovTop.PullLat

module

public import Formalism.SatakeDualWeyl.StatementE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

def IsInt {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r s : Type}
    (M : Matrix r s (w.adicCompletion E)) : Prop :=
  ∀ i j, M i j ∈ Ov E w

def coef (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  (c : ℂ) ^ (i * b + j * a) * (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j)

def pairs (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal k).filter fun p => p.1 ≤ a ∧ p.2 ≤ b

theorem mem_pairs {a b k : ℕ} {p : ℕ × ℕ} : p ∈ pairs a b k ↔ p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [pairs, Finset.mem_filter]

theorem IsInt.add {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M N : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M + N) :=
  fun i j => (Ov E w).add_mem (hM i j) (hN i j)

theorem IsInt.neg {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) : IsInt w (-M) :=
  fun i j => (Ov E w).neg_mem (hM i j)

theorem isInt_zero {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r s : Type) :
    IsInt w (0 : Matrix r s (w.adicCompletion E)) :=
  fun _ _ => (Ov E w).zero_mem

def intSub {E : Type} [Field E] [NumberField E] (a b : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w X}
  zero_mem' := isInt_zero w _ _
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg

def latM {E : Type} [Field E] [NumberField E] {a b : ℕ} {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E)
    (m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val))}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using isInt_zero w _ _
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_add]; exact h1.add h3
    · rw [Matrix.add_mul, smul_add]; exact h2.add h4
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_neg]; exact h1.neg
    · rw [Matrix.neg_mul, smul_neg]; exact h2.neg

def latD {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E) (a b i j : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {W | ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w}
  zero_mem' := by
    intro r s
    simp only [Matrix.zero_apply, mul_zero, ite_self]
    exact (Ov E w).zero_mem
  add_mem' := by
    intro X Y h1 h2 r s
    have e1 := h1 r s
    have e2 := h2 r s
    simp only [Matrix.add_apply]
    split_ifs at e1 e2 ⊢
    · rw [mul_add]; exact (Ov E w).add_mem e1 e2
    · exact (Ov E w).add_mem e1 e2
  neg_mem' := by
    intro X h1 r s
    have e1 := h1 r s
    simp only [Matrix.neg_apply]
    split_ifs at e1 ⊢
    · rw [mul_neg]; exact (Ov E w).neg_mem e1
    · exact (Ov E w).neg_mem e1

end GlobalTheory.CompanionTheory.CtS

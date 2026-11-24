module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def topR {P : M.Par} (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (y : ℝ) : ℂ :=
  Wd.qw (M.qC P) (D.positionted w) (y : ℂ) / Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) e ((y : ℂ) + 1)

def TopRatio : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → 28 * Real.exp 1 ≤ Cc → ∀ (v : Fin S.f) (w : List C.Letter) (y : ℝ),
    KB.CutWord (D.parOf S v) (S.l + 1) ((true, y) :: w) → (∃ m, y ∈ S.grid v m) → w.length < S.Ntop →
    (∀ x ∈ w, (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - x.2| ∧ (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - (x.2 - 1)|)) →
    ∀ (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)),
      0 < (topR (S.l + 1) w e ρ y).re ∧ (topR (S.l + 1) w e ρ y).im = 0 ∧
      |S.P v y| ≤ Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (Real.sqrt (S.T * S.T'))⁻¹ * (topR (S.l + 1) w e ρ y).re

def lamTop {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (b : ℕ) (v : Fin S.f) : ℝ :=
  √((2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r b ((S.G.r : ℤ) + 2 - b))) * Real.exp 1 *
    (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
    (√(S.T * S.T'))⁻¹)

def TopLocB : Prop :=
  KB.DegTop → Top.VecVTypes → TopRatio →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v, 0 ≤ lamTop S (S.G.r + 2 - s) v ∧
      2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.TopLoc (setC S p F) v fun b _ => lamTop S b v

end

end Formalism.FourierDecayAlt.P.PBL

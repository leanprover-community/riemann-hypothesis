module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut

namespace PI.UnitaryGroupMassFormula.HwConjInf

def HwUniqAt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam mu : Fin n → ℤ),
    a.HWAt τ lam → a.HWAt τ mu → lam = mu

def ConjSwap : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ),
    a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i))

def ratPt {L : Type} [Field L] {n : ℕ} (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => p.1 (γ₀ p.2.1 p.2.2)

def InV {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (y : (L →+* ℂ) × Fin n × Fin n → ℂ) : Prop :=
  ∀ σ : L →+* ℂ, ∃ B : GL (Fin n) ℂ, ∀ i j,
    y (σ, i, j) = B.val i j ∧ y (ComplexEmbedding.conjugate σ, i, j) = (B⁻¹).val j i

def DensStep : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

def gPt {n : ℕ} (g : GL (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then g.val p.2.1 p.2.2 else (g⁻¹).val p.2.2 p.2.1

def GLStep : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ),
    (∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j)) →
    (∀ g h, R (g * h) = R g * R h) →
    ∀ (S : Set (Matrix ι ι ℂ)), (∀ s ∈ S, ∀ g, s * R g = R g * s) →
    ∀ (v u : ι → ℂ) (lam mu : Fin n → ℤ),
    (∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v) →
    (∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u) →
    Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} = ⊤ →
    Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} = ⊤ →
    v ≠ 0 → u ≠ 0 → lam = mu

def GlueStep : Prop := DensStep → GLStep → HwUniqAt

end PI.UnitaryGroupMassFormula.HwConjInf

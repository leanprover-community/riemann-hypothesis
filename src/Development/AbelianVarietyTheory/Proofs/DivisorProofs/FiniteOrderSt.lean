module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic

def ConstSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ m : Pic A.left, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∀ ψ : A ⟶ A, IsMonHom ψ → GlobalTheory.EffBound.Eff (m - t • pull ψ.left (cls L hL)) → ψ = 1

def CubeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ (c : Pic A.left) (x y z : A ⟶ A),
      pull (x * y * z).left c + pull x.left c + pull y.left c + pull z.left c =
        pull (x * y).left c + pull (x * z).left c + pull (y * z).left c + pull (1 : A ⟶ A).left c

def FiniteOrderSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ σ : A ≅ A, IsMonHom σ.hom →
      pull σ.hom.left (cls L hL) = cls L hL → ∃ m : ℕ, m ≠ 0 ∧ (GlobalTheory.SerreField.iter σ m).hom = 𝟙 A

def SeparatedSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ q : ℕ, 2 ≤ q → ∀ u : A ⟶ A,
      (∀ k : ℕ, ∃ ψ : A ⟶ A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1

def SerreAmpleSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ N : ℕ, 3 ≤ N → (N : K) ≠ 0 →
      ∀ σ : A ≅ A, IsMonHom σ.hom → pull σ.hom.left (cls L hL) = cls L hL →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A), x ^ N = 1 → x ≫ σ.hom = x) →
      σ.hom = 𝟙 A


end GlobalTheory.AmpleRigid

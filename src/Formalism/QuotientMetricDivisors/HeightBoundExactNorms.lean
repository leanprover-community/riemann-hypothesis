module

public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HarderNarasimhan.QuotRealize
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

open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

section Defs

def fnorm {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ :=
  Formalism.HermitianLatticesTheory.cnorm (Y⁻¹.mulVec x)

def fmaj {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i, star (Y⁻¹.mulVec x i) * Y⁻¹.mulVec y i

def pairC {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (x : Fin a → ℂ) (y : Fin D → ℂ) : ℂ :=
  ∑ i, ∑ k, x i * y k * v.embedding (B (Pi.single i 1) (Pi.single k 1))

def chainFun {m : ℕ} {C : Fin (m + 1) → Type} (Kj : ∀ j : Fin m, C j.castSucc → C j.succ) :
    ∀ i : Fin (m + 1), C 0 → C i :=
  Fin.induction (motive := fun i => C 0 → C i) id (fun j f => Kj j ∘ f)

def chainMat {R : Type} [Semiring R] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) R) :
    ∀ i : Fin (m + 1), Matrix (Fin (c i)) (Fin (c 0)) R :=
  Fin.induction (motive := fun i => Matrix (Fin (c i)) (Fin (c 0)) R) 1 (fun j A => Kj j * A)

def minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

end Defs

def FnormRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K),
      fnorm (X v) (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ∧
      fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (y i)) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y ∧
      ((fnorm (X v) (fun i => v.embedding (x i)) ^ 2 : ℝ) : ℂ) =
        fmaj (X v) (fun i => v.embedding (x i)) (fun i => v.embedding (x i))

def OpNormDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (a D : ℕ)
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ v, IsUnit (XM v).det) → (∀ v, IsUnit (XE v).det) →
    ∀ (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) (v : InfinitePlace K) (c : ℝ), 0 ≤ c →
      (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) v B ≤ c ↔
        ∀ (x : Fin a → ℂ) (y : Fin D → ℂ), ‖pairC v B x y‖ ≤ c * fnorm (XM v) x * fnorm (XE v) y)

def CompNormAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K,
      (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) v (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∏ j : Fin m, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j))) ∧
      (chainMat Kj (Fin.last m) ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
          (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        ∑ j : Fin m, Formalism.HN.htMap (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (Matrix.mulVecLin (Kj j)))

def SminLog : Prop :=
  ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (κ : ℝ) (lam : J → Ix → ℝ), 0 < κ →
    (∀ j p, 0 < lam j p) →
      0 < κ * minOver (fun p => ∏ j, lam j p) ∧
      (∀ p, κ * minOver (fun p => ∏ j, lam j p) ≤ κ * ∏ j, lam j p) ∧
      (∃ p, κ * minOver (fun p => ∏ j, lam j p) = κ * ∏ j, lam j p) ∧
      Real.log (κ * minOver (fun p => ∏ j, lam j p)) =
        Real.log κ + minOver (fun p => ∑ j, Real.log (lam j p))

def HeightBoundConstant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (κ : InfinitePlace K → ℝ) (lam lamL : J → Ix → InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    (∀ j p v, 0 < lamL j p v) → (∀ j p v, lamL j p v ≤ lam j p v) →
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((κ v * ∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
    ∀ (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ),
    (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) →
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
        Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) -
          minOver (fun p => ∑ j, Real.log (lamL j p v))) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2)) -
          (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lamL j p v)) - meanLog κ

end Formalism.DivisionValues

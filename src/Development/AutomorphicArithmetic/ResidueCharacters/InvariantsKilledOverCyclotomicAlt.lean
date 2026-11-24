module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

def sN (l N : ℕ) : ℕ := max 1 (N.factorization l)

def lamN (l N h : ℕ) : ℕ := sN l N + Nat.log l (2 * h) + Nat.log l N + 1

def eL (l N h : ℕ) : ℕ := 32 * (2 * h * sN l N + 1) + lamN l N h

def c0L (l N h n : ℕ) : ℕ := 20 * (n + 1) * lamN l N h

def cBL (l N h n t : ℕ) : ℕ := 40 * (t + 1) * (n + 1) * lamN l N h

variable {l : ℕ} [Fact l.Prime]

structure Cyc (N : ℕ) (K LL : FinExt l) : Prop where
  lvl : l = 2 → 4 ∣ N
  pos : 0 < N
  le : K.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ Nat.lcm l N = 1}
  coef : ∀ x : Om l, x ^ Nat.lcm l N = 1 → x ∈ LL.1

variable (P : LocPrime l)

def LiftK : Prop := ∀ (N h : ℕ) (K LL : FinExt l), Cyc N K LL →
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) → F.LiftF (P.PD K) (eL l N h)


set_option synthInstance.maxHeartbeats 400000 in
def InvariantsKilledOverCyclotomic : Prop := ∀ (N h n : ℕ) (K LL : FinExt l), Cyc N K LL →
  ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : Finset ℤ), U.card ≤ n → (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) →
    IsCrys (P.PD K) T.ρ → (∀ τ, JumpsInV (P.PD K) T.ρ τ (U : Set ℤ)) → (∀ τ, ¬ IsJumpV (P.PD K) T.ρ τ 0) →
    ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((l : ↥(OL LL)) ^ c0L l N h n) • x = 0

def TBK : Prop := ∀ (N h n t : ℕ) (K LL : FinExt l), Cyc N K LL → t ≤ h →
  ∀ (J : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Set ℤ) (U : Finset ℤ), U.card ≤ n → (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) →
    (∀ τ, J τ ⊆ (U : Set ℤ)) → TBAt (P.PD K) (O := ↥(OL LL)) (IK K) J t (cBL l N h n t)

end UpperTheory.N

end

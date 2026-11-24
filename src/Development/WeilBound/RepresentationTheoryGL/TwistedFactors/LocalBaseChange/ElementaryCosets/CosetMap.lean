module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace PositivityTheory.Lbc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ones (N : ℕ) : Fin N → ℕ := fun _ => 1

theorem sum_ones (N : ℕ) : ∑ a, ones N a = N := by simp [ones]


variable (k) in
abbrev torEmb (N : ℕ) : Levi k (Bl (ones N)) →* GL (Fin N) k := leviEmb k (stdBlocks (ones N) (sum_ones N))


variable (k) in
def Tor (N : ℕ) : Subgroup (GL (Fin N) k) := (torEmb k N).range


variable (k) in
def Nup (N : ℕ) : Subgroup (GL (Fin N) k) := unipRad k (stdBlocks (ones N) (sum_ones N))


variable (k) in
def Nlo (N : ℕ) : Subgroup (GL (Fin N) k) := unipRadLower k (stdBlocks (ones N) (sum_ones N))

def tnorm {G : Type} [Group G] (θ : MulAut G) (l : ℕ) (x : G) : G :=
  (List.ofFn fun i : Fin l => (θ ^ (i : ℕ)) x).prod

def dcos {G : Type} [Group G] (J : Subgroup G) (t : G) : Set G :=
  {g | ∃ a ∈ J, ∃ b ∈ J, g = a * t * b}


variable (k) in
def DomT (N : ℕ) (J : Subgroup (GL (Fin N) k)) (x : GL (Fin N) k) : Prop :=
  ∃ s, torEmb k N s = x ∧ IsDominant k N J (ones N) (sum_ones N) s


variable (k) in
def StrDomT (N : ℕ) (J : Subgroup (GL (Fin N) k)) (x : GL (Fin N) k) : Prop :=
  ∃ s, torEmb k N s = x ∧ IsStrictlyDominant k N J (ones N) (sum_ones N) s ∧
    ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U →
      ∃ j : ℕ, ∀ n ∈ KNl k N J (ones N) (sum_ones N), (x ^ j)⁻¹ * n * x ^ j ∈ U


variable (k) in
def admitted (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) : Prop :=
  IsOpen (J : Set (GL (Fin N) k)) ∧ IsCompact (J : Set (GL (Fin N) k)) ∧
    HasIwahoriFact k N J (ones N) (sum_ones N) ∧ Continuous θ ∧ 0 < l ∧ θ ^ l = 1 ∧
    J.map θ.toMonoidHom = J ∧ (Nup k N).map θ.toMonoidHom = Nup k N ∧
    (Nlo k N).map θ.toMonoidHom = Nlo k N ∧ (Tor k N).map θ.toMonoidHom = Tor k N


variable (k) in
def GoodT (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k) : Prop :=
  t ∈ Tor k N ∧ (∀ i < l, DomT k N J ((θ ^ i) t)) ∧ StrDomT k N J (tnorm θ l t)


variable (k) in
def IncrV (N : ℕ) (x : GL (Fin N) k) : Prop :=
  ∀ i j : Fin N, i < j →
    valuation k ((x : Matrix (Fin N) (Fin N) k) i i) < valuation k ((x : Matrix (Fin N) (Fin N) k) j j)



variable (k) in
def E1 : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ g ∈ dcos J t, ∃ j ∈ J, ∃ κ ∈ J ⊓ Tor k N, g = j⁻¹ * (t * κ) * θ j




end PositivityTheory.Lbc

end

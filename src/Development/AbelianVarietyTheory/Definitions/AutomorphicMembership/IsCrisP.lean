module

public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def IsEps (e : Per.Fl l) : Prop :=
  e.untilt = 1 ∧ ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ≠ 1

def rootT (e : Per.Fl l) (m : ℕ) : Per.OC l := (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt

def xi (e : Per.Fl l) : Per.Ainf l :=
  ∑ i ∈ Finset.range l, (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) ^ i

def mu (e : Per.Fl l) : Per.Ainf l := Per.tm e - 1

def aDp (l : ℕ) [Fact l.Prime] : Per.Ainf l →+* Per.BdRp l :=
  (algebraMap (Per.AinfP l) (Per.BdRp l)).comp (algebraMap (Per.Ainf l) (Per.AinfP l))

def phiA (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Acris l := GlobalTheory.CrisMaps.frob l

def sigA (g : Per.Gq l) : Per.Acris l →+* Per.Acris l := GlobalTheory.CrisMaps.gal g

def IsLogA (e : Per.Fl l) (y : Per.Acris l) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ s : Per.Acris0 l,
    ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1) ∧
    ∃ z : Per.Acris l, y - algebraMap (Per.Acris0 l) (Per.Acris l) s = ((l : ℕ) : Per.Acris l) ^ r * z

structure IsCrisP (j : Per.Acris l →+* Per.BdRp l) : Prop where
  on0 : ∀ a : Per.Acris0 l, j (algebraMap (Per.Acris0 l) (Per.Acris l) a) =
    algebraMap (Per.AinfP l) (Per.BdRp l) (a : Per.AinfP l)
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Per.Ainf l,
    Per.ev l n (((l : ℕ) : Per.BdRp l) ^ N * j x) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)

structure IsSec (o : Om l →+* Per.BdRp l) : Prop where
  th : ∀ x : Om l, Per.θD l (o x) = ((x : Om l) : ℂ_[l])
  z : ∀ z : ℤ_[l], o (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = aDp l (Per.zA l z)

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

structure Core (l : ℕ) [Fact l.Prime] where

  ζ : ℕ → Om l
  ζ_zero : ζ 0 = 1
  ζ_succ : ∀ m, ζ (m + 1) ^ l = ζ m
  ζ_one : ζ 1 ≠ 1
  ε : Per.Fl l
  ε_root : ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m)

  o : Om l →+* Per.BdRp l
  o_sec : IsSec o

  j : Per.Acris l →+* Per.BdRp l
  j_cris : IsCrisP j
  ι : Per.Bcris l →+* Per.BdR l
  ι_j : ∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)

  u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l
  ι_u : ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l))

  t : Per.Acris l
  t_log : IsLogA ε t

  σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)
  σ_root : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l

  χ : GQ l →* ℤ_[l]ˣ
  χ_cyc : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val

end

end GlobalTheory.MemLoc

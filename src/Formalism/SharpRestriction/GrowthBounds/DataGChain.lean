module

public import Formalism.SharpRestriction.GrowthBounds.DataG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.G

namespace Places

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def Tminus (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) : P.Tup → P.Xsp :=
  fun L => ∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L'', L v⟩),
    F (Function.update L v L'')

def withWt (m' : ℕ) (lam0' : ∀ v, Fin (P.n' v) → Fin (m' + 1) → ℤ) (dom' : ∀ v, IsDominant (lam0' v)) :
    Places p O Kf :=
  { P with m := m', lam0 := lam0', dom := dom' }

end Places

def liftWt (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) : Fin (m + j * (t + 1) + 1) → ℤ :=
  fun i => if h : i.val < m + 1 then lam ⟨i.val, h⟩ else -(w ((i.val - (m + 1)) / (t + 1) + 1))

structure Fills {p : ℕ} (G : GAtP p) where
  TT : ∀ v : Fin G.P.nV, Finset (Fin (G.P.n' v))
  a : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → ℤ
  b : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → ℤ
  c : ℕ
  base : ∀ v, IsBaseWeight (TT v) (a v) (b v) c (G.P.lam0 v)
  t : ℕ
  mm : ℕ
  w : ∀ v : Fin G.P.nV, ℕ → Fin (G.P.n' v) → ℤ
  w_ge : ∀ v s, max (c : ℤ) (-(G.P.lam0 v s (Fin.last G.P.m))) ≤ w v 1 s
  w_mono : ∀ v s j, 1 ≤ j → w v j s ≤ w v (j + 1) s
  domJ : ∀ j v, IsDominant fun s => liftWt t G.P.m (G.P.lam0 v s) (fun i => w v i s) j

namespace Fills

variable {p : ℕ} {G : GAtP p} (Fl : Fills G)

def Pj : ℕ → Places p G.O G.Kf
  | 0 => G.P
  | j + 1 => G.P.withWt (G.P.m + (j + 1) * (Fl.t + 1))
      (fun v s => liftWt Fl.t G.P.m (G.P.lam0 v s) (fun i => Fl.w v i s) (j + 1)) (Fl.domJ (j + 1))

end Fills

structure Levels {p : ℕ} {G : GAtP p} (Fl : Fills G) where
  compS : ℕ → Type
  [finS : ∀ j, Fintype (compS j)]
  levS : ∀ j, compS j → Level (Fl.Pj (j + 1))

attribute [instance] Levels.finS

namespace Levels

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl)

def comp : ℕ → Type
  | 0 => G.comp
  | j + 1 => Lv.compS j

def lev : (j : ℕ) → Lv.comp j → Level (Fl.Pj j)
  | 0 => G.lev
  | j + 1 => Lv.levS j

abbrev Fm (j : ℕ) : Type := Lv.comp j → (Fl.Pj j).Tup → (Fl.Pj j).Xsp

def Int (j : ℕ) : Submodule G.O (Lv.Fm j) := Submodule.pi Set.univ fun i => (Lv.lev j i).M

def Tm (j : ℕ) (v : Fin (Fl.Pj j).nV) (i : ℕ) (F : Lv.Fm j) : Lv.Fm j := fun c => (Fl.Pj j).Tminus v i (F c)

end Levels

structure Chain {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) where
  Kz : ∀ j, Lv.Fm j →ₗ[G.Kf] Lv.Fm (j + 1)

namespace Chain

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl} (Ch : Chain Lv)

def chainK : (j : ℕ) → Lv.Fm 0 →ₗ[G.Kf] Lv.Fm j
  | 0 => LinearMap.id
  | j + 1 => (Ch.Kz j).comp (chainK j)

end Chain

end Formalism.MainNotions.G

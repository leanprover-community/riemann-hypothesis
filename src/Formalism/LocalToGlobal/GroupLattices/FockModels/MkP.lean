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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def mkP (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) : Places p O Kf where
  w := w
  nV := 1
  n' := fun _ => n'
  W := fun _ => W
  Qq := fun _ => Qq
  ι := fun _ => ι
  σ := fun _ => σ
  j := fun _ => j
  setting := fun _ => h
  m := m
  r := r
  lam0 := fun _ => lam0
  dom := fun _ => hd

def mkG (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) : GAtP p where
  O := O
  Kf := Kf
  P := mkP h m r lam0 hd
  comp := Empty
  lev := fun i => i.elim
  e := 0

end

end Formalism.L2.G.Model

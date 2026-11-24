module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
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

open ArithmeticFunction

namespace HostParam

structure AbField where
  N : ℕ
  N_pos : 0 < N
  H : Subgroup (ZMod N)ˣ

namespace AbField

variable (E : AbField)

abbrev Gal : Type := (ZMod E.N)ˣ ⧸ E.H

def res : (ZMod E.N)ˣ →* E.Gal := QuotientGroup.mk' E.H

def IsReal : Prop := (-1 : (ZMod E.N)ˣ) ∈ E.H

def inertiaUnits (p : ℕ) : Subgroup (ZMod E.N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd E.N p)).ker

def inertia (p : ℕ) : Subgroup E.Gal := (E.inertiaUnits p).map E.res

def Ramified (p : ℕ) : Prop := E.inertia p ≠ ⊥

def IsModulus (M : ℕ) : Prop := ∃ h : M ∣ E.N, (ZMod.unitsMap h).ker ≤ E.H

noncomputable def conductor : ℕ := sInf {M : ℕ | E.IsModulus M}

def chars : Set (DirichletCharacter ℂ E.N) := {χ | ∀ u ∈ E.H, χ (u : ZMod E.N) = 1}

noncomputable def toGalChar (χ : DirichletCharacter ℂ E.N) (hχ : χ ∈ E.chars) : E.Gal →* ℂˣ :=
  QuotientGroup.lift E.H χ.toUnitHom (fun u hu => by
    rw [MonoidHom.mem_ker]; ext; simpa using hχ u hu)

end AbField

def SplitsIn (d p : ℕ) : Prop :=
  p ≠ d ∧ (p = 2 → d % 8 = 7) ∧ (p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1)

noncomputable def quadCharNeg (d : ℕ) : DirichletCharacter ℂ d :=
  if h : d.Prime then
    letI : Fact d.Prime := ⟨h⟩
    (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  else 1

noncomputable def AbField.chOf (E : AbField) (d : ℕ) (h : d ∣ E.N) : DirichletCharacter ℂ E.N :=
  DirichletCharacter.changeLevel h (quadCharNeg d)

end HostParam

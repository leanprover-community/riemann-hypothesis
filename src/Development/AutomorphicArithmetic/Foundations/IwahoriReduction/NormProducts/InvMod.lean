module

public import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.Kd.K4

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def InvMod (X : Tower Ω ε) (M m : ℕ) (a : X.Kˣ) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ h : X.Kˣ, X.sl (ofSL γ) (a : X.K) = a * (h : X.K) ^ m


open Classical in
def img (Γ : Subgroup SL(2, ℤ)) (M : ℕ) [NeZero M] : Finset SL(2, ZMod M) :=
  Finset.univ.filter fun γ => γ ∈ Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

def trM (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a : X.Khat l) : X.Fn l :=
  ∑ γ ∈ img (Gam N l) M, X.act l ((g * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) fun u => (u 0) ^ w • a

def CgF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a b : X.Fn l) : Prop :=
  ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (a u - b u) = 0

def Rep (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.Kˣ) (x : X.Khat l) : Prop :=
  AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n a

def PolMod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l) : Prop :=
  ∃ c : Fin (w + 1) → X.Khat l, (∀ i, ∃ f ∈ X.Un (l ^ n), Rep X l n f (c i)) ∧
    ∀ u, t u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i

end UpperTheory.Kd.K4

end

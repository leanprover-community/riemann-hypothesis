module

public import Formalism.WachModuleLifts.StatementW
public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.CoboundaryTransfers.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace Formalism.CoboundaryTransfers

open Formalism

section CL

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

variable {B : CL.W.Base p A} {η : ℕ}

variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']

end CL

section CLback

def Base.QLin {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) : Prop :=
  B.Q = B.X + (B.p : A)

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

def toCL (B : Base ℤ_[p] A) (hp : B.p = p) (hq : B.QLin) (hφ : B.PhiX (p - 1)) :
    CL.W.Base p A where
  φA := B.φ
  γA := B.γ
  π₀ := B.X
  q := B.Q
  hq := by simpa [Base.QLin, hp] using hq
  hφ := hφ
  comm := B.comm

def WachMod.toCL {B : Base ℤ_[p] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] (W : WachMod B M D) (hp : B.p = p)
    (hq : B.QLin) (hφ : B.PhiX (p - 1)) : CL.W.WachMod (toCL B hp hq hφ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  π₀_inj := W.X_inj
  q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_qN := W.γ_QN

end CLback

section LIFT

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]

variable {B : LIFT.Base ℓ A} {M : ℕ}

def toLIFT (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q)
    (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) : LIFT.Base ℓ A where
  φA := B.φ
  γA := B.γ
  X := B.X
  Q := B.Q
  u := u
  comm := B.comm
  φX := hφ
  γX := hγX
  γQ := by
    obtain ⟨v, hv, ⟨t, rfl⟩, hγ⟩ := hγQ
    exact ⟨t, hv, by rw [hγ, mul_comm]⟩

def WachMod.toLIFT {B : Base ℤ_[ℓ] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : WachMod B M D) (u : ℤ_[ℓ]ˣ)
    (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.WD (toLIFT B u hφ hγX hγQ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N

end LIFT

end Formalism.CoboundaryTransfers

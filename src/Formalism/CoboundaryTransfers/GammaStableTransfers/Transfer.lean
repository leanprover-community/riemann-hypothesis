module

public import Formalism.CoboundaryTransfers.StatementBridge
public import Formalism.CoboundaryTransfers.StatementTransfer
public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section Maps

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℤ_[ℓ] A} {M : ℕ}

def homToLIFT {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.Hom (W.toLIFT u hφ hγX hγQ) (W'.toLIFT u hφ hγX hγQ) where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le

def sesToLIFT {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂} (S : SES W₀ W₁ W₂)
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.SES (W₀.toLIFT u hφ hγX hγQ) (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) where
  ι := homToLIFT S.ι u hφ hγX hγQ
  π := homToLIFT S.π u hφ hγX hγQ
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

end Maps

theorem wachLatticeUnramified_statement : LemmaUU := by
  intro ℓ _ A _ _ B M u hp hφ hγX hγQ D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK hRS
  have hCK' : LIFT.CokerKilled (sesToLIFT S u hφ hγX hγQ) e := by
    intro n hn
    have := hCK n hn
    rw [hp] at this
    exact this
  have hRS' : LIFT.RatSurj (sesToLIFT S u hφ hγX hγQ) := by
    intro y z hyz
    have := hRS y z hyz
    rw [hp] at this
    exact this
  exact LIFT.lift_LemmaU ℓ A (toLIFT B u hφ hγX hγQ) M D₀ D₁ D₂ (W₀.toLIFT u hφ hγX hγQ)
    (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) (sesToLIFT S u hφ hγX hγQ) e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK' hRS'

end Formalism.CoboundaryTransfers

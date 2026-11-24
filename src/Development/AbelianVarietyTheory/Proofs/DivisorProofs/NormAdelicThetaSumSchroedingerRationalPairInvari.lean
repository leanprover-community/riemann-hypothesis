module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaRatInv

theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

theorem thetaSum_schr_rat_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (a b : κ → F)
    (w : (κ → AF F) × (κ → AF F)) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ ((fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i)) + w) Φ) =
      ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ (fun i => algebraMap F (AF F) (b i)) - (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ w.2)) *
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ) := by
  set ra : κ → AF F := fun i => algebraMap F (AF F) (a i) with hra
  set rb : κ → AF F := fun i => algebraMap F (AF F) (b i) with hrb
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : κ → F => ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ rb - ra ⬝ᵥ w.2)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  set rξ : κ → AF F := fun i => algebraMap F (AF F) (ξ i) with hrξ
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rξ + ra := by
    funext i; simp [hrξ, hra]
  have e3 : ∀ c d : κ → F, (fun i => algebraMap F (AF F) (c i)) ⬝ᵥ (fun i => algebraMap F (AF F) (d i)) =
      algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [dotProduct]
  rw [e1]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hx : rξ + (ra + w.1) = rξ + ra + w.1 := (add_assoc _ _ _).symm
  rw [hx]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  conv_rhs => rw [← mul_one (ψ _), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq', ← e3, ← e3]
  simp only [add_dotProduct, dotProduct_add]
  have t : ∀ z : AF F, ⅟(2 : AF F) * z + ⅟(2 : AF F) * z = z := fun z => by
    rw [← add_mul, invOf_two_add_invOf_two, one_mul]
  linear_combination t (ra ⬝ᵥ w.2)

theorem norm_thetaSum_schr_ratPair_add : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).mp hγ
  rw [thetaSum_schr_rat_add ψ hψ.2.2.1 Φ a b w, norm_mul, hψ.2.1, one_mul]

end GlobalTheory.ThetaRatInv

end

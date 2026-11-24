module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end

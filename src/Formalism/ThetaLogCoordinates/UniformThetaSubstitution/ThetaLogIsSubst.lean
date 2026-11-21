import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WChain
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGaussK
import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ThetaLogIsSubstitution
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.PlacesAddClass

section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def EdgeExponent : Prop :=
  ∀ (ι : Type) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj X : ι → ℤ) (i : ℕ),
    NprimeZ Ev Od lam wj i + ∑ s ∈ Ev, ((i : ℤ) * wj s - X s) + ∑ s ∈ Od, (X s - (i : ℤ) * wj s) =
      ∑ s ∈ Od, X s + ∑ s ∈ Ev, (∑ a ∈ Icc 1 i, (lam s a + wj s) - X s)

def EdgeNonneg : Prop :=
  ∀ (μ : YoungDiagram) (B : Type) [DecidableEq B] (I : ℕ → Finset B) (J : Finset B),
    (∀ c, (I c).card = μ.colLen c) →
    ∑ c ∈ range (μ.rowLen 0), (I c ∩ J).card ≤ ∑ a ∈ range J.card, μ.rowLen a

end Formalism.InvariantFactorPaths.G7
end
end

section
namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7


theorem kernel_from_k_one_k : KernelBoundsGeneric := kernel_bounds_generic

end Formalism.InvariantFactorPaths.G7.Top
end

section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

structure PlaceData (K : Type) (r0 r1 : ℕ) where

  ν : ℕ

  hν : NeZero ν

  u : ZMod (2 * ν) → K

  TT : Finset (ZMod (2 * ν))

  ξ : ZMod (2 * ν) → Fin r0 → K

  e : TpV ν r1 → ℕ

  C : ℕ

  l : Fin C → ℕ

  sf : Fin C → ZMod (2 * ν)

  T : ∀ c, Fin (l c) → Fin r0 → K

  I : ∀ c, Fin (l c) → Fin r1

  J : Finset (Fin r1)

  kind : Fin 3

attribute [instance] PlaceData.hν

namespace PlaceData

variable {K : Type} {r0 r1 : ℕ}

def op [Field K] (D : PlaceData K r0 r1) : MvPolynomial (ZV D.ν r0 r1) K :=
  entryOp D.ξ D.e D.l D.sf D.T D.I

def pay (D : PlaceData K r0 r1) : ℕ :=
  if D.kind = 2 then
    ∑ x : TpV D.ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ D.J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ D.J)
      then D.e x else 0) +
    ∑ c, (if (D.sf c).val % 2 = 1 then ((univ.image (D.I c)) ∩ D.J).card else 0)
  else 0

def bound (D : PlaceData K r0 r1) (p : ℕ) : ℝ :=
  (if D.kind = 0 then
    excessGain (p : ℝ) D.TT (dSet D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf))
  else if D.kind = 1 then
    gainG (p : ℝ) D.TT (oddT D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf)) - ∑ s ∈ D.TT \ oddT D.TT, (alN D.e s : ℝ)
  else
    gainG (p : ℝ) D.TT (oddT D.TT) (fun s => (alN D.e s : ℝ)) (fun s => (capN D.sf s : ℝ))
      (deLoss p r0 r1 D.TT (alN D.e) (lsN D.l D.sf))) +
  rhoP p * ∑ s, ((alN D.e s : ℝ) + lsN D.l D.sf s)

def OK [NormedField K] (D : PlaceData K r0 r1) : Prop :=
  (∀ s, ‖D.u s‖ ≤ 1) ∧ (∀ s a, ‖D.ξ s a‖ ≤ 1) ∧ (∀ c i a, ‖D.T c i a‖ ≤ 1) ∧
    ∀ x : TpV D.ν r1, x.1 ∉ D.TT → D.e x = 0

end PlaceData

def EntryMulti : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype Pl] [DecidableEq Pl]
    (p r0 r1 : ℕ) (ϖ : K) (D : Pl → PlaceData K r0 r1), p.Prime → 2 < p →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ v, (D v).OK) →
    ∀ U : MvPowerSeries (Σ v, ZV (D v).ν r0 r1) K, Integral U →
      ‖(p : K) ^ (∑ v, (D v).pay) *
        jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (D v).op)
          ((∏ v, atPlace (ι := fun v => ZV (D v).ν r0 r1) v
            (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hhS p (D v).u)))) * U)‖ ≤
        (p : ℝ) ^ (-(∑ v, (D v).bound p))

end Formalism.InvariantFactorPaths.G7
end
end

section
namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem thetaLogIsSubst : ThetaLogIsSubst := by
  intro K _ ν r0 r1 _ om oms ϖ μ Tht hμ

  have hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
    intro x
    unfold zLin
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs <;> simp
  have hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)

  have hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 := by
    intro x
    unfold sSub
    rw [PowerSeries.constantCoeff_subst (hz x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases d with _ | d
    · simp [hμ]
    · simp [map_pow, hz0 x]
  have ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])
  have hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 =>
      MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)
  exact MvPowerSeries.subst_comp_subst_apply ha hb Tht

end Formalism.InvariantFactorPaths.G7.Top
end

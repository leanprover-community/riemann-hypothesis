module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.CbStrictMonoOfAnti
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem linearMap_coeAddMonoidHom_eq_mapRange_smul {ι : Type*} [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (S : ι → Submodule ℂ W) (L : W →ₗ[ℂ] W) (a : ι → ℂ) (hL : ∀ i, ∀ y ∈ S i, L y = a i • y)
    (f : DirectSum ι (fun i => S i)) :
    L (DirectSum.coeAddMonoidHom S f) = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange.addMonoidHom (fun i => DistribSMul.toAddMonoidHom (S i) (a i)) f) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of, hL i y y.2]
    change _ = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange _ (fun j => map_zero _) (DFinsupp.single (β := fun j => S j) i y))
    rw [DFinsupp.mapRange_single]
    change _ = DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i _)
    rw [DirectSum.coeAddMonoidHom_of]
    rfl
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem vanish_match (hBr : Branching) {P : M.Par} (hP : P.OK) {Wp : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hπ : IsType P.k P.r z π P.u)
    {e : Fin (2 * P.r + P.k + 1) → ℂ} (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hBs : IsFrameOf P.k P.r [z, e] Bs) (hlin : ∀ w : ℂ, IsLinearMap ℂ (capRep P.k P.r π Bs w))
    {x : Wp} (hx : x ≠ 0) (μ : ℂ → ℂ) (hμ : ∀ w : ℂ, capRep P.k P.r π Bs w x = μ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∃ ρ : M.Ty (Pq P), ∀ Y : ℂ, μ Y = M.xC (Pq P) ρ Y := by
  obtain ⟨S, hS, -, hcap⟩ := hBr Wp (Pq P) (Pq_OK hP) rfl z e π hz hT hπ he hez hee
  obtain ⟨d, hd⟩ := hS.2 x
  obtain ⟨ρ, hρ⟩ : ∃ ρ, d ρ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by rw [← hd, show d = 0 from DFinsupp.ext h, map_zero])
  refine ⟨ρ, fun Y => ?_⟩
  have hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := add_sub_cancel_right _ _
  have h1 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (IsLinearMap.mk' _ (hlin (Y + ((P.k : ℂ) - 2) / 2)))
    (fun σ => M.xC (Pq P) σ Y)
    (fun σ y hy => (hcap Bs hBs σ _ y hy).trans (congrArg (fun t => M.xC (Pq P) σ t • y) hw)) d
  have h2 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (μ Y • LinearMap.id) (fun _ => μ Y) (fun _ _ _ => rfl) d
  have h3 : (DFinsupp.mapRange.addMonoidHom fun i =>
        DistribSMul.toAddMonoidHom (S i) (M.xC (Pq P) i Y)) d =
      (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (μ Y)) d :=
    hS.1 (by
      rw [← h1, ← h2, hd]
      simpa [hw] using hμ (Y + ((P.k : ℂ) - 2) / 2))
  have h4 := congrArg (fun f => f ρ) h3
  simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply,
    DistribSMul.toAddMonoidHom_apply] at h4
  exact (smul_left_injective ℂ hρ h4).symm

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfBack
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstRaisingMemEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def LocInt (x : Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ l ∈ X.B.I.L, iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈ OpX X p ∧
    iota2 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈ OpX X p

def LocGlob : Prop :=
  ∀ x : Fin X.B.I.n → X.B.I.E, LocInt X p θ x → (fun j => iota2 X p θ (x j)) ∈ Mlat2 X p θ

def ApproxP : Prop :=
  ∀ z : Fin X.B.I.n → FpX X p, (∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p) →
    ∃ x : Fin X.B.I.n → X.B.I.E, LocInt X p θ x ∧ z - (fun j => iota2 X p θ (x j)) ∈ Mlat2 X p θ

theorem dualBack_of (h1 : LocGlob X p θ) (h2 : ApproxP X p θ) : DualBack X p θ := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := h2 z hz
  have h := Submodule.add_mem _ hzx (h1 x hx)
  rwa [sub_add_cancel] at h

def DenomP : Prop :=
  ∀ e : X.B.I.E, iota1 X p θ e ∈ OpX X p → iota2 X p θ e ∈ OpX X p →
    ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ c : 𝓞 X.B.I.E, (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * e

theorem secondEmbedding_algebraMap (f : X.B.I.F) : iota2 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
  have h1 : inclR (FpX X p) (algebraMap X.B.I.F X.B.I.E f) =
      algebraMap (FpX X p) (TpX X p) (algebraMap X.B.I.F (FpX X p) f) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : X.B.I.E →ₐ[X.B.I.F] TpX X p).commutes f
  have h2 := congrArg Prod.snd (th_incl (X := X) (p := p) (θ := θ) (algebraMap X.B.I.F X.B.I.E f))
  simp only at h2
  rw [← h2, h1, AlgEquiv.commutes]
  rfl

theorem unit_of_notMem (t : 𝓞 X.B.I.F) (ht : t ∉ p.1.asIdeal) :
    (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹ ∈ OpX X p ∧ algebraMap X.B.I.F (FpX X p) (t : X.B.I.F) ≠ 0 := by
  have hle : p.1.intValuation t ≤ 1 := p.1.intValuation_le_one t
  have hnlt : ¬ p.1.intValuation t < 1 := fun h => ht ((p.1.intValuation_lt_one_iff_mem t).mp h)
  have hval : Valued.v (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F)) = 1 := by
    have e1 : Valued.v (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F)) = p.1.intValuation t := by
      first
      | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := X.B.I.F) p.1
          (t : X.B.I.F)).trans
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := X.B.I.F) p.1 t)
      | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := X.B.I.F) p.1 t).trans
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := X.B.I.F) p.1 t)
    rw [e1]
    exact le_antisymm hle (not_lt.mp hnlt)
  have hne : algebraMap X.B.I.F (FpX X p) (t : X.B.I.F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  refine ⟨?_, hne⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]

theorem hform_smul_right (y x : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y (c • x) = c * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Loc

end MassDataIdxSteps

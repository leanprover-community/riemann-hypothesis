module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamPlaced

section Prim

open GlobalTheory.FinPl

theorem incA_mul_mem_intAt {D : D7} (v : GlobalTheory.FinPl.Pl D) (c : D.host.E) (N : ℤ) (hint : IsIntegral ℤ (N • c))
    (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) {a : AE D} (ha : a ∈ intAt D (· = v)) : incA D c * a ∈ intAt D (· = v) := by
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hv, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

theorem prim_std {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i)) (v : GlobalTheory.FinPl.Pl D)
    (z : Fin S.rank → D.host.E) (hz : ∀ i, IsIntegral ℤ (z i)) (i₀ : Fin S.rank) (π' : D.host.E) (hπ' : IsIntegral ℤ π') (N : ℤ)
    (hπ : z i₀ * π' = (N : D.host.E)) (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    a • ratV z ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ a ∈ intAt D (· = v) := by
  have hL' : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i := fun x => by
    rw [hL x]
    exact ⟨fun h i => ⟨⟨x i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNE : (N : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hN
  have hz0 : z i₀ ≠ 0 := fun h => hNE (by rw [← hπ, h, zero_mul])
  have h1 : ((1 : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rw [Int.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  rw [GlobalTheory.FinPl.Model.mem_latV_std S L hL' v]
  constructor
  · intro h
    have hi : a * incA D (z i₀) ∈ intAt D (· = v) := h i₀
    have hint : IsIntegral ℤ (N • (z i₀)⁻¹) := by
      have : N • (z i₀)⁻¹ = π' := by
        rw [zsmul_eq_mul, ← hπ, mul_comm (z i₀), mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      rw [this]; exact hπ'
    have h2 := incA_mul_mem_intAt v (z i₀)⁻¹ N hint hv hi
    rwa [mul_comm a, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul] at h2
  · intro h i
    show a * incA D (z i) ∈ intAt D (· = v)
    rw [mul_comm]
    exact incA_mul_mem_intAt v (z i) 1 (by rw [one_smul]; exact hz i) h1 h

end Prim

end GlobalTheory.FamPlaced
end

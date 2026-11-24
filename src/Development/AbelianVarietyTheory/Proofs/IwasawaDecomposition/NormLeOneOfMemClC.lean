module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

end GlobalTheory.Mem.Df

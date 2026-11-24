module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GalClose

open GlobalTheory.CuspRep

theorem isSSRep_rankOne {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 1) k) : IsSSRep ρ := by
  intro W _
  by_cases h : W = ⊥
  · refine ⟨⊤, fun g v _ => Submodule.mem_top, ?_⟩
    rw [h]; exact isCompl_bot_top
  · have hW : W = ⊤ := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      have h0 : v 0 ≠ 0 := fun e => hv0 (funext fun j => by rw [Subsingleton.elim j 0, e]; rfl)
      refine eq_top_iff.2 fun u _ => ?_
      have : u = (u 0 / v 0) • v := funext fun j => by
        rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
      rw [this]; exact W.smul_mem _ hv
    refine ⟨⊥, fun g v hv => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hv ⊢; rw [hv]; exact Matrix.mulVec_zero _
    · rw [hW]; exact isCompl_top_bot

end GlobalTheory.GalClose

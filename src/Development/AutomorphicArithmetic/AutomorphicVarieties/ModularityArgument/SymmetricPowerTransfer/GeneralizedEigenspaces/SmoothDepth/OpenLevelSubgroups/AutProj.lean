module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

open GlobalTheory.DefU in
theorem UpperTheory.V.Z.Sym.Al.autProj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (M : Submodule ℂ (GlobalTheory.DefU.autU L n)), FiniteDimensional ℂ M →
        ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA L n → ℂ)) (P : κ → GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n),
          (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧
          (∀ i x φ, P i (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P i φ)) ∧ ∀ φ ∈ M, ∑ i, P i φ = φ := by
  intro L _ _ _ n M hM
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable L n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary L n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA L n) (ratU L n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form L n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU L n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA L n) (autU L n) (autRep L n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU L n)), (∀ σ, IsAutRepU σ → σ.comap (autU L n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA L n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU L n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU L n).subtype).map (autU L n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU L n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU L n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU L n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU L n).subtype).map (autU L n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU L n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]

module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvFormStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.IsoComp

open GlobalTheory.CompRed

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoTyp_indep (a : NG.AlgWt L n) {ι : Type} (S : ι → Submodule ℂ (GAf L n → a.W))
    (hS : ∀ i, NG.IsIrrRep a.ρ (S i)) (hinj : ∀ i j, NG.IsoRep (S i) (S j) → i = j) :
    iSupIndep fun i => NG.isoTyp a.ρ (S i) := by
  classical
  haveI hW : FiniteDimensional ℂ a.W := a.alg.1
  have hT := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  have hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) := by
    intro M hM
    haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ hT hM
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ M) (Submodule.span_le.2 ?_)
    rintro f ⟨hf, hκ⟩
    exact ⟨hf.1, hκ⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.algWt_exists_invForm' L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson L n a β hβ
  have hG : GlobalTheory.TypeOrthogonality.Good a.ρ B := hB
  exact indep_of_orth (fun x => B x) _ (fun i x hx h0 => pos_zero hG (isoTyp_le _ hx) h0)
    (fun i j hij => isoTyp_orth hG hfin (hS i) (hS j) (fun h => hij (hinj i j h)))

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_mem_isoTyp {ρ : Representation ℂ (GQ L n) W} (S : Submodule ℂ (GAf L n → W))
    (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) : NG.heckeD J Dset f ∈ NG.isoTyp ρ S := by
  classical
  rw [GlobalTheory.HeckeScalarAll.heckeD_eq_sum J Dset hfin]
  refine Submodule.sum_mem _ fun c _ => ?_
  split_ifs with hc
  · exact isoTyp_stable S _ f hf
  · exact Submodule.zero_mem _

theorem heckeD_finset_sum {ι : Type} (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (s : Finset ι) (F : ι → GAf L n → W) :
    NG.heckeD J Dset (∑ i ∈ s, F i) = ∑ i ∈ s, NG.heckeD J Dset (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.HeckeScalarAll.heckeD_zero J Dset hfin]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.HeckeScalarAll.heckeD_add' J Dset hfin, ih]

end Gen

end GlobalTheory.IsoComp

end

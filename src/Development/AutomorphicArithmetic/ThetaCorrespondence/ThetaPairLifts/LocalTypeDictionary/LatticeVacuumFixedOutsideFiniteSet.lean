module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVprimeStabilizerFixesVacuum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VacuumFixedBySplitSphericalLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LatStabVac
theorem lattice_vacuum_fixed_outside_finite_set : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum hP F E σ B a a' G X om om' hT
  obtain ⟨S₂, hS₂⟩ := _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum hP F E σ B a a' G X om om' hT
  refine ⟨X.T ∪ S₁ ∪ S₂, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvT, hv₁⟩, hv₂⟩ := hv
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hT.base v with hs | ⟨w, hw⟩
  · exact ⟨hS₁ v hv₁ hs, hS₂ v hv₂ hs⟩
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
    · exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hT v w hw hvT k hk
end GlobalTheory.LatStabVac
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | exact _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | (intros; apply _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set <;> assumption)
end

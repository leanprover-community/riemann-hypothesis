module

public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemH1fIffResMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleDescentToTameSubextensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, GlobalTheory.T.wach_lattice_expansion_at_low_level_points D HW F Cm, GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm,
    GlobalTheory.T.wachModule_saturated_exactness_crystalline D HW F Cm, GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F, GlobalTheory.T.p8_of_cmpOf D HW F Cm, GlobalTheory.T.wachModule_descent_to_tame_subextension D HW F,
    GlobalTheory.T.wachModule_uniqueness_characterisation D HW F, GlobalTheory.T.gammaSemisimpleQuotientD_statement D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F, GlobalTheory.T.defect_torsion_second_cohomology_kernel D HW F Cm,
    GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, GlobalTheory.T.local_comparison_of_cmpOf D HW F Cm⟩

end GlobalTheory.NL

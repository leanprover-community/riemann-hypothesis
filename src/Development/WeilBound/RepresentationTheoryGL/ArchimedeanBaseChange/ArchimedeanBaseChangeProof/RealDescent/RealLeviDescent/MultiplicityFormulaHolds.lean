import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.FirstSubSecondLeviFamily
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundarySquareLeviReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanishingKernelLeviReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestriction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDecompositionLevi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionUnipotentRadicalReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPickReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviStabilityReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRelationsReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfAction

section
namespace PositivityTheory.RgBcC.RealD

theorem injective_decomposition_action_holds : InjectiveDecompositionAction :=
  injective_decomposition_action_of GlobalTheory.T.boundary_square_levi_real GlobalTheory.T.vanishing_kernel_levi_real GlobalTheory.T.injective_restriction_of_bdsq_vanish GlobalTheory.T.injective_unipotent_of_restriction (hcdecL_of GlobalTheory.T.harish_chandra_decomposition_levi) GlobalTheory.T.action_unipotent_radical_real

theorem hc_decomposition_levi_holds : HCdecLv := GlobalTheory.T.harish_chandra_decomposition_levi

end PositivityTheory.RgBcC.RealD
end

section
namespace PositivityTheory.RgBcC.RealD

theorem multFor_of (hP : InvPick) (hLS : LevStab) (hLR : LevRel) (hSC : SemiCls) (hCC : CapCls) (h4 : LeviCommutantWordReduction)
    (h5 : CapelliProductsScalar) : MultFor :=
  multiplicity_assembly_holds hP injective_decomposition_action_holds.1 hc_decomposition_levi_holds injective_decomposition_action_holds.2.2 hLS hLR hSC hCC h4 h5

end PositivityTheory.RgBcC.RealD
end

section
namespace PositivityTheory.RgBcC.RealD

theorem multFor_of_capCls (hCC : CapCls) : MultFor :=
  multFor_of GlobalTheory.T.invariant_pick_real GlobalTheory.T.levi_stability_real GlobalTheory.T.levi_relations_real GlobalTheory.T.semisimple_classification_real hCC GlobalTheory.T.commutant_reduction_real GlobalTheory.T.scalar_action_fifth_real

end PositivityTheory.RgBcC.RealD
end

section
namespace PositivityTheory.RgBcC.RealD

theorem multiplicity_formula_holds : MultFor :=
  multFor_of_capCls (GlobalTheory.T.capelli_classification_of_action injective_decomposition_action_holds.2.2)

end PositivityTheory.RgBcC.RealD
end

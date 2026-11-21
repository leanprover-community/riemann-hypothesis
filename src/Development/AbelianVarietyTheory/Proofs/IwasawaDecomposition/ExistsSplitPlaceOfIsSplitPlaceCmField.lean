import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.SplitPlaceOf

theorem exists_splitPlace : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P →
    ∃ s : SplitPlace D.host.E, s.w = P :=
  fun D P hP => GlobalTheory.RowUnitProof.exists_splitPlace_eq D P hP

end GlobalTheory.HeightCounting.SplitPlaceOf
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P → ∃ s : SplitPlace D.host.E, s.w = P := by
  atlas_forward_decl GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace

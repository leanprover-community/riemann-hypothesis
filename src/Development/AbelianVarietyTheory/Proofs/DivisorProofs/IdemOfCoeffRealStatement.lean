module

public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffReal
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.star_idemOf_coeff_eq_self : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ) (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X → ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  first | exact @GlobalTheory.CuspMult.idemOf_coeff_real

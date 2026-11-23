module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLawsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelsOfSemistableReduction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExistStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChangeStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem partI_of_semistableReduction_of_arcFam :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ArcFamSt → PartI :=
  fun S A => by
    obtain ⟨L, L2, L3, L4, L5, L6⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
    exact GlobalTheory.T.modelSystems_jointProperties_of_laws GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange L L2 L3 L4 L5 L6 GlobalTheory.LN.ega_holds
      GlobalTheory.uniformisation_dvr_unconditional GlobalTheory.T.linearUniformisation_triples_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing A
      (GlobalTheory.modelsSt_of_semistableReduction S) GlobalTheory.T.siegelFamilies_exist

end GlobalTheory

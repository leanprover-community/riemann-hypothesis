module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairExistenceOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PairIt
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
theorem exists_seesaw_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  intro hPr D S S' aS aT hP V W M M' θ ψ hθ
  have hD := hPr.discreteSeriesCover
  have hH := hPr.harishChandraModules
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ =>
    exists_locIt_pair hX h1 h2 hB M M' τ (hP τ)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, fun ω ⟨χS, χT, hω, he⟩ f hf => ?_⟩
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2
end GlobalTheory.PairIt
end
end

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  first | exact @_root_.GlobalTheory.PairIt.exists_seesaw_pair | exact _root_.GlobalTheory.PairIt.exists_seesaw_pair | (intros; apply _root_.GlobalTheory.PairIt.exists_seesaw_pair <;> assumption)
end

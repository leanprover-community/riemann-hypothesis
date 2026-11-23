module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UniformModerateGrowthLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.CuspDecay

theorem bounded_of_smooth_unifModGrowth : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth V θ φ → IsCuspFun V φ → ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  intro hP D θ V hθ φ ha hs hg hc
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hs' := (GlobalTheory.SmoothForms.smooth_iff R φ).1 hs
  exact (hP D θ hθ V _ (GlobalTheory.SmoothForms.isExpFam_expInf R) φ ha hs'
    ((GlobalTheory.SmoothForms.growth_iff hθ R ha hs').1 hg) hc).bounded

end GlobalTheory.CuspDecay

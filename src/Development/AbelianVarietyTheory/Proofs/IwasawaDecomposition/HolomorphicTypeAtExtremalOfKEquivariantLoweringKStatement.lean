module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringK
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.holomorphicType_at_extremal_of_kEquivariant_loweringKilled : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  first | exact @GlobalTheory.KMapHol.holAd_of_kEquiv | exact GlobalTheory.KMapHol.holAd_of_kEquiv | (intros; apply GlobalTheory.KMapHol.holAd_of_kEquiv <;> assumption)

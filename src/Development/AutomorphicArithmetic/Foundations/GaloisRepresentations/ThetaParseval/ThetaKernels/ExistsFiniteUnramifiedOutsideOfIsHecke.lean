module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlaces
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA

@[expose] public section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
theorem UpperTheory.exists_finite_unramified_outside_of_isHecke :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ {χ : Chr F E}, IsHecke F E χ → ∃ S : Finset (Pl F), UnrOff χ (S : Set (Pl F)) := by
  intro F E _ _ _ _ _ σ B hB χ hχ
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ UnrAt χ w}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.PairVac.eventually_unrAt_of_isHecke σ hB.cm χ hχ)
  refine ⟨(hfin.image fun w => w.under (𝓞 F)).toFinset, fun w hw => ?_⟩
  by_contra hu
  exact hw (by
    show w.under (𝓞 F) ∈ (((hfin.image fun w => w.under (𝓞 F)).toFinset : Finset (Pl F)) : Set (Pl F))
    rw [Set.Finite.coe_toFinset]
    exact ⟨w, hu, rfl⟩)
end

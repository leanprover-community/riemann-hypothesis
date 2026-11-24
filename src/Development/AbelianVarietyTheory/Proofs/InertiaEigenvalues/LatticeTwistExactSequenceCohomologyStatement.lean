module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomology
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_twist_exact_sequence_cohomology : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  first | exact @GlobalTheory.TensIsoExt.tensIso_of_exact | exact GlobalTheory.TensIsoExt.tensIso_of_exact | (intros; apply GlobalTheory.TensIsoExt.tensIso_of_exact <;> assumption)

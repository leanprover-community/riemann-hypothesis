module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol

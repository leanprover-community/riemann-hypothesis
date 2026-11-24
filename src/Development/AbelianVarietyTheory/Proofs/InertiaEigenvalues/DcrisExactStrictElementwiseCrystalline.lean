module

public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (GlobalTheory.T.ramifiedCoefficientChains_adm11 D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory

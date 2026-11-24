module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1

namespace GlobalTheory.CompanionTheory.HeckeFin

variable (L : Type) [Field L] [NumberField L]

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem continuous_infIdele : Continuous (infIdele L) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : (InfiniteAdeleRing L)ˣ → InfiniteAdeleRing L) :=
  Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace L, v.Completion)

theorem denseRange_units :
    DenseRange (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom : Lˣ → (InfiniteAdeleRing L)ˣ) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨l, w, hw, hl⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open
    ((isOpenEmbedding_val L).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero] at hl
    exact w.ne_zero hl
  exact ⟨w, hw, Units.mk0 l hl0, Units.ext hl.symm⟩

variable {L}

end GlobalTheory.CompanionTheory.HeckeFin

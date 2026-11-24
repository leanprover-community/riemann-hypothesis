module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]

def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter

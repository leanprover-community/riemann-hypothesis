module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsPrimeSpanXb
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section GenPt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotientMap_imageZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    Function.Injective (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
      (le_refl (imageZ v W'))) :=
  Ideal.quotientMap_injective' le_rfl


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
instance imageZ_isPrime (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] :
    (imageZ v W').IsPrime :=
  Ideal.IsPrime.comap _

def genFibreOf (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] : GenFibre v W' :=
  letI g : MRing ι ⧸ imageZ v W' →+* FnField W' :=
    (algebraMap (MRing ι' ⧸ W') (FnField W')).comp
      (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom (le_refl (imageZ v W')))
  have hg : Function.Injective g :=
    (IsFractionRing.injective (MRing ι' ⧸ W') (FnField W')).comp (quotientMap_imageZ_injective v W')
  letI alg : Algebra (FnField (imageZ v W')) (FnField W') :=
    (IsFractionRing.lift (K := FnField (imageZ v W')) hg).toAlgebra
  { Φ := FnField (imageZ v W')
    Φ' := FnField W'
    alg := alg
    x := genPt (imageZ v W')
    x' := genPt W'
    ker_x := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk (imageZ v W')) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ imageZ v W') c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W') f
    compat := fun p => by
      show genPt W' (v p) = IsFractionRing.lift hg (genPt (imageZ v W') p)
      rw [genPt, genPt, IsFractionRing.lift_algebraMap]
      simp [g, Ideal.quotientMap_mk] }

theorem GenericPointExists.proof : GenericPointExists.Statement := by
  intro K _ ι _ K' _ ι' _ v W' hW'
  exact ⟨genFibreOf v W'⟩

end GenPt

end GroundTheory.Heights₂.Heights.Inter

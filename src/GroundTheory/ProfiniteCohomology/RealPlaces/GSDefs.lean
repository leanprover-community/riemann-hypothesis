module

public import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

instance fintype_gal_infAlgClosure (v : InfinitePlace K.1) :
    Fintype Gal(AlgebraicClosure v.Completion / v.Completion) :=
  inferInstance

def gsRealFamily (v : {v : InfinitePlace K.1 // v.IsReal}) :
    Gal(AlgebraicClosure v.1.Completion / v.1.Completion) →ₜ* galUnramifiedOutside K.1 ℚ̄ S :=
  ⟨decompHomS v.1.Completion S (ιr v), continuous_decompHomS (Kv := v.1.Completion) S (ιr v)⟩

theorem gsRealFamily_apply (v : {v : InfinitePlace K.1 // v.IsReal})
    (σ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    ιr v ((gsRealFamily S ιr v σ y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = σ (ιr v y) :=
  decompHom_apply ((ιr v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ y

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

abbrev gsTateCompactCohomology (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (n : ℕ) : ModuleCat (ULift.{0} ℤ) :=
  tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) M n

abbrev gsRealRes (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] (n : ℕ) :=
  globalToLocal (gsRealFamily S ιr) M (fun v => Rep.res (gsRealFamily S ιr v).toMonoidHom M)
    (fun _ => CategoryTheory.CategoryStruct.id _) n

end

end GroundTheory.ProfCoh

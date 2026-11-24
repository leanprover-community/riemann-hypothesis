module

public import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import GroundTheory.ProfiniteCohomology.DiscreteModules
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import Mathlib.Tactic.Linter.HaveILetI
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable def resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield) [Fact (K ≤ K')]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) :
    Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) := by
  letI : IsScalarTower K.1 K'.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Rep.res (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom
    (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)

instance isDiscreteRep_resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield)
    [Fact (K ≤ K')] (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] :
    IsDiscreteRep (resTo S K' hK' M) := by
  unfold resTo
  have : IsScalarTower K.1 K'.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isDiscreteRep_res_subtype M (gsOpenSubgroup S hK' : Subgroup _)
  exact IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom (gsBaseChange S hK').symm) _

end PositivityTheory.Lit1.GEN.W_killed_a

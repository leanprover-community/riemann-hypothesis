module

public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
import Formalism.ConjugateSelfDual.Statement
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

namespace GlobalTheory.CompanionTheory.GSCd

theorem cdp_le_of_continuousMulEquiv {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ)
    (e : G ≃ₜ* H) : cdp p G ≤ cdp p H := by
  refine cdp_le_iff.2 fun A _ hA q hq => ?_
  let φ : H ≃* G := e.toMulEquiv.symm
  have he : Continuous φ.toMonoidHom := e.continuous_invFun
  have he' : Continuous φ.symm.toMonoidHom := e.continuous_toFun
  let B : Rep.{0} (ULift.{0} ℤ) H := Rep.res φ.toMonoidHom A
  haveI : IsDiscreteRep B := IsDiscreteRep.res he A
  have hB : IsAddTorsion B := hA
  have hH := primaryComponent_cohomology_eq_bot_of_cdp_lt B hB hq
  haveI := isIso_cohomologyMapAlong_of_mulEquiv φ he he' (𝟙 B) Function.bijective_id q
  let F := asIso (cohomologyMapAlong φ.toMonoidHom he (𝟙 B) q)
  rw [primaryComponent_eq_bot_iff] at hH ⊢
  rintro x ⟨k, hk⟩
  have h0 : F.toLinearEquiv x = 0 :=
    hH _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  exact F.toLinearEquiv.injective (h0.trans (map_zero _).symm)

theorem cdp_eq_of_continuousMulEquiv : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ), (G ≃ₜ* H) → cdp p G = cdp p H := by
  intro G H _ _ _ _ _ _ p e
  exact le_antisymm (cdp_le_of_continuousMulEquiv p e) (cdp_le_of_continuousMulEquiv p e.symm)

end GlobalTheory.CompanionTheory.GSCd

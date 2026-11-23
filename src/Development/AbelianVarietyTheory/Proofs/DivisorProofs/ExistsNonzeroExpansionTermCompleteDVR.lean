module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ExpansionNonzero

theorem exists_term_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  intro V _ _ _ hV D' A' G' _ _ U' U₀ _ σ' f' hf ⟨j, hj⟩
  have := hV.1
  have := U'.semi.smooth
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have := FibreNonzero.isIso_snd_left G'
  have : IsReduced (𝟙_ _ ⊗ G').left := isReduced_of_isOpenImmersion (snd (𝟙_ _) G').left
  have h : (𝟙_ _ ⊗ G').left.basicOpen (σ'.f j) ≠ ⊥ := fun h => hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  refine GlobalTheory.SectionUnif.exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf y ?_
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

end GlobalTheory.ExpansionNonzero

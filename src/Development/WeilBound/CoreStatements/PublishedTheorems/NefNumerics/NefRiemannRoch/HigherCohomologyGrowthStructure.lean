module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCutsStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDimsStatement
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

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem hdim_twist_structureModule_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hproj d L hL hkd hind i hi
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, f, hf, -⟩ := hproj
    haveI := hf
    exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ PSpace.str k N)
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (suppDim_structureModule (X := X)).trans_le hkd
  by_cases hsec : ∃ p, 1 ≤ p ∧ HasNonzeroSec (lbPow L p)
  · obtain ⟨p, hp, s, hs⟩ := hsec
    have hmono : Mono (cutHom (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB p) s) :=
      (mono_cutHom_structureModule_iff _ s).mpr ((sec_ne_zero_iff s).mp hs)
    exact T.higherCohomology_twist_bound_of_regular_section k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp p hp s hmono i hi
  · push_neg at hsec
    have h0 : ∀ m, 1 ≤ m → hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 = 0 := by
      intro m hm
      by_contra hne
      exact hsec m hm (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) (Nat.pos_of_ne_zero hne))
    have hint := T.nef_intersection_nonneg_all_dims k X hproj (d + 1) (GlobalTheory.structureModule X) hsupp (fun _ => L) (fun _ => hL)
    have hi2 := T.higherCohomology_twist_bound_of_two_cuts k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp
    rcases Nat.lt_or_ge i 2 with h | h
    · obtain rfl : i = 1 := by omega
      exact T.h1_dim_bound_of_no_sections_nonneg_interNum k X hproj d L hL.isLB (GlobalTheory.structureModule X) hsupp h0 hint hi2
    · exact hi2 i h

end GlobalTheory.NefRR

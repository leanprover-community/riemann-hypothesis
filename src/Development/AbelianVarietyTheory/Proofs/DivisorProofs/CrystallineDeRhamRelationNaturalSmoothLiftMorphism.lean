module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeOneDifferCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeTwoDifferCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeOneClassPullbackOfCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeTwoClassPullbackOfCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatTransLiftsOverAffinePairsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LiftNat



theorem main : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  refine ⟨?_, ?_⟩
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' ⟨k, f, w, hc, hh, hk, hw⟩ ⟨k', f', w', hc', hh', hk', hw'⟩
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeOne_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h1 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z1 k) : (KK D'.κ D'.t).H1) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p1 k.1 - k'.1) = -((morMap m).p1 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h1 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h1 (QuotientAddGroup.mk k') := by
      rw [(GlobalTheory.CxCoh.joinedOne_inst.2.1 _ _ θ (CxMap.joined_pre _ θ)).2, pairB, CxMap.cohomOne_pullback_comp, e1]
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z1 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H1) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z1 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p1 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1) = _
    abel
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' hr hr'
    obtain ⟨k, f, w, hc, hh, hk, hw⟩ := hr
    obtain ⟨k', f', w', hc', hh', hk', hw'⟩ := hr'
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h2 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z2 k) : (KK D'.κ D'.t).H2) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p2 k.1 - k'.1) = -((morMap m).p2 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h2 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h2 (QuotientAddGroup.mk k') := by
      have j := GlobalTheory.CxCoh.JoinedTwoProof.main ((pairB Λ' φ m).pre θ) (pairB Λ' φ m) θ (CxMap.joined_pre _ θ)
        (QuotientAddGroup.mk k)
      refine j.trans ?_
      have j2 := CxMap.cohomTwo_pullback_comp (morMap m) ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)) (QuotientAddGroup.mk k)
      refine j2.trans ?_
      exact congrArg _ e1
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z2 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H2) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z2 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p2 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) = _
    abel

end GlobalTheory.PDForm.LiftNat

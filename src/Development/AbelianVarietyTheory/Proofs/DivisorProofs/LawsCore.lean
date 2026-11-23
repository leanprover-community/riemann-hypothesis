module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LawsCore

theorem laws_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) →
    Laws (T.U j) (xiR D) := by
  intro D T hT j hj hF
  have hg : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hLaws : GlobalTheory.LevGeo.Laws D j (T.Q.Xo j) T.Q.c (T.U j) (GlobalTheory.LevGeo.coreDict T.toCore j) := by
    obtain ⟨hH, hL, _, hDat⟩ := hT.pins
    refine ⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
      obtain ⟨Kf', hr', h1, h2, h3⟩ := GlobalTheory.LevCore.dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (GlobalTheory.LevGeo.coreDict T.toCore j σ)
        (fun g h' => by unfold GlobalTheory.LevGeo.coreDict; rw [dite_eq_left h']) (T.Kf j σ) th hr _
        (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
      exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
    · intro σ hσ
      have h := hT.modelW j hj σ hσ
      rw [hT.spaceW j hj σ hσ] at h
      exact h
  exact (GlobalTheory.LevLaws.laws_of_level D j _ _ _ (T.Q.Xo j) T.Q.c (T.U j) _
    hLaws hF hg).1

end GlobalTheory.LawsCore

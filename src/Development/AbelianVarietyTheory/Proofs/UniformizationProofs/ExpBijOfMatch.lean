module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BijectiveOfIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansionStatement
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k
  have ht := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause

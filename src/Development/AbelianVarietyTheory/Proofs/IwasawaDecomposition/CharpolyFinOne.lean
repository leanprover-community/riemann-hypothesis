module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RhoDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR


end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting


end GlobalTheory.HeightCounting

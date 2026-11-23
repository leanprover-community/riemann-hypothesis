module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.MaximalUnramified
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.LocalFields.UnitsPowers
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import GroundTheory.ProfiniteCohomology.ProcyclicDefs

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Dict

theorem isFrob_of_unramifiedDegree_eq_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  intro F Ω _ _ _ _ _ A v _ hA ι σ g hσ hι hg
  refine (GlobalTheory.FrobTeich.isFrob_iff_teichmuller F Ω A v hA σ).2 ⟨hσ, fun z m hm hz => ?_⟩
  have hcard : Nat.card 𝓀[v.adicCompletion F] = normV v := by
    rw [GroundTheory.Global.natCard_residueField_adicCompletion, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have hfrob := (unramifiedDegree_eq_ofAdd_one_iff g).1 hg
  rw [hcard] at hfrob
  have hq : 1 < normV v := hcard ▸ one_lt_card_residueField (v.adicCompletion F)
  suffices h : ι (σ z) = ι (z ^ normV v) from (RingHom.injective ι.toRingHom) h
  rw [hι, map_pow]
  have hξ : (ι z) ^ normV v ^ m = ι z := by rw [← map_pow, hz]
  by_cases h0 : ι z = 0
  · rw [h0, map_zero, zero_pow (by omega)]
  · refine hfrob _ ⟨m, hm.ne', mul_right_cancel₀ h0 ?_⟩
    have e : normV v ^ m = (normV v ^ m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hcard, ← pow_succ, ← e, hξ, one_mul]

end GlobalTheory.CompanionTheory.Dict

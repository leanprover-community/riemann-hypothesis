import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff

section
namespace GlobalTheory.ClosureDimensionSpecialization

open Order TopologicalSpace Topology

theorem dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by
  intro X z w j hzw hne hdim
  have hsub : closure ({w} : Set X) ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw))
      isClosed_closure
  have hind : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  haveI : IrreducibleSpace (closure ({z} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  let top : IrreducibleCloseds (closure ({z} : Set X)) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top := by
    intro a
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro h
    have hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈
        (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) := by
      rw [h]; exact Set.mem_univ _
    have hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} :=
      isClosed_closure.preimage continuous_subtype_val
    have hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆
        {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} := by
      rw [IrreducibleCloseds.coe_map]
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hwz : w ⤳ z := specializes_iff_mem_closure.mpr (hsub' hz)
    exact hne ((hzw.antisymm hwz).eq).symm
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have h1 : height a + 1 ≤ height top :=
    calc height a + 1 ≤ height (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a) + 1 := by
          gcongr
          exact height_le_height_apply_of_strictMono _
            (IrreducibleCloseds.map_strictMono_of_isInducing hind) a
      _ ≤ height top := height_add_one_le (hlt a)
  have h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞) := by
    rw [← hdim]; exact height_le_krullDim top
  have h3 : height top ≤ ((j : ℕ∞) + 1) := by exact_mod_cast h2
  have h4 : height a ≤ (j : ℕ∞) :=
    (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)
  exact_mod_cast h4

end GlobalTheory.ClosureDimensionSpecialization
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_le_of_specializes :
    ∀ (X : Scheme.{0}) (z w : X) (j : ℕ), z ⤳ w → w ≠ z →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      topologicalKrullDim (closure ({w} : Set X)) ≤ j := by
  first
  | exact @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | (apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes ..)

end GlobalTheory.PairStep
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_and_lcAt_antitone_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  first | exact @GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | exact GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | (intros; apply GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
  GlobalTheory.PairStep.logCanonicalCut_of_step
end
end

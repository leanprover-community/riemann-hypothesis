module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

theorem mapToLocalization_mem_tangentDerivations (M : Submonoid S) [IsLocalization M S']
    {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by
  have hD' := (mem_tangentDerivations k P D).mp hD
  rw [mem_tangentDerivations]
  intro x hx
  refine derivation_apply_mem_of_mem_span (D.mapToLocalization (S' := S') M)
    (G := algebraMap S S' '' (P : Set S)) le_rfl ?_ hx
  rintro _ ⟨p, hp, rfl⟩
  rw [Derivation.mapToLocalization_algebraMap]
  exact Ideal.mem_map_of_mem _ (hD' p hp)

theorem map_logDerivIdeal_le (M : Submonoid S) [IsLocalization M S'] (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)
  · intro D hD x hx
    rw [Ideal.mem_comap]
    have h : algebraMap S S' (D x) =
        (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
      rw [Derivation.mapToLocalization_algebraMap]
    rw [h]
    exact derivation_apply_mem_logDerivIdeal k _ _ _
      (mapToLocalization_mem_tangentDerivations (S' := S') k M hD)
      (Ideal.mem_map_of_mem _ hx)

theorem exists_mem_tangentDerivations_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by
  have hDt := (mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD
  obtain ⟨m₀, D₀, hD₀⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    · have hgP : g ∈ P := by
        rw [← hG]
        exact Ideal.subset_span (Finset.mem_coe.mpr hg)
      have h1 : algebraMap S S' g ∈ P.map (algebraMap S S') := Ideal.mem_map_of_mem _ hgP
      have h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S') := hDt _ h1
      have h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S') := by
        rw [← hD₀ g]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨n, hnM, hn⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff M S' P (D₀ g)).mp h3
      exact ⟨⟨n, hnM⟩, fun _ => hn⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by
    refine ⟨Finset.prod G (fun g => ((f g : S))),
      Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg
    have h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ (hf g hg)
  refine ⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩
  · rw [mem_tangentDerivations]
    intro x hx
    refine derivation_apply_mem_of_mem_span (c • D₀) hG.le ?_ (hG.symm ▸ hx)
    exact fun g hg => hcP g (Finset.mem_coe.mp hg)
  · intro s
    change algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s) = algebraMap S S' (c * D₀ s)
    rw [map_mul, map_mul, mul_assoc, hD₀ s]

theorem logDerivIdeal_map_le_map_logDerivIdeal (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩
  intro D hD x hx
  obtain ⟨m, D₁, hD₁, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨⟨⟨y, hy⟩, t⟩, hxt⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := S')).mp hx
  have hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S') :=
    Ideal.map_mono (le_logDerivIdeal k P J) hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp only [smul_eq_mul] at h1
  have e1 := hm y
  have e2 := hm (t : S)
  have hmul : algebraMap S S' ((m : S) * (t : S)) * D x
      = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + e1 - x * e2
  have hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    refine sub_mem ?_ ?_
    · exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)
    · exact Ideal.mul_mem_right _ _ hxL
  have hu : IsUnit (algebraMap S S' ((m : S) * (t : S))) := by
    rw [map_mul]
    exact (IsLocalization.map_units (M := M) (S := S') m).mul
      (IsLocalization.map_units (M := M) (S := S') t)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hmem

theorem logDerivIdeal_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)

theorem logDerivIdealIterate_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]

theorem logDerivIdeal_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  logDerivIdeal_map k (Submonoid.powers g) hP J

theorem logDerivIdealIterate_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) :=
  logDerivIdealIterate_map k (Submonoid.powers g) hP r J

end FunctorialResolution.EmbeddedResolution

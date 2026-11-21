import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair.Model

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}






theorem simple_pole (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    ¬ Klt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 ∧
      EffAt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 := by
  have h0 : (t : K)⁻¹ ≠ 0 := inv_ne_zero fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_inv, E.ord_irreducible ht]
  norm_num

theorem simple_zero (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    Klt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 ∧
      ¬ EffAt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 := by
  have h0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_irreducible ht]
  norm_num


section Scheme

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}



theorem exists_klt_smooth [PerfectField k] [SmoothOfRelativeDimension n p]
    (hn : topologicalKrullDim X = n) (x : X) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn p) n (locRing x) η φ := by
  haveI := SmoothOfRelativeDimension.smooth n p
  obtain ⟨η, m, g, -, -, h⟩ := (kltAt_iff_exists_klt (p := p) (n := n) 0 x).1
    (kltAt_zero_of_smooth hn x)
  exact ⟨isLocModel_locRing x, η, _, h⟩

end Scheme

theorem projectiveSpace (d : ℕ) (x : (ProjVar.proj ℂ d).X) :
    IsLocModel (Cartier.constFn (ProjVar.proj ℂ d).str) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn (ProjVar.proj ℂ d).str) (ProjVar.proj ℂ d).dim (locRing x) η φ :=
  exists_klt_smooth (ProjVar.Var.topologicalKrullDim_eq _) x


theorem exists_chart [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ t u : E.ring, Irreducible t ∧ IsUnit u ∧ IsUnit (u - 1) ∧
      IsFreeGen E.ring (dForm E.const ![t, u]) := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, hz, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : m = 1 := by
    have : 2 = m + 1 := by exact_mod_cast h2
    omega
  have key (w : E.ring) (hw : KaehlerDifferential.D k E.ring w = b 1) : IsUnit w := by
    by_contra hu
    have hm : w ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hm
    rw [Derivation.leibniz, ← hz, ← hb 0] at hw
    have := congrArg (fun η => b.repr η 1) hw
    simp at this
    exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (hz ▸ this))
  have ez : z = ![t, z 1] := by
    funext i
    fin_cases i
    · exact hz
    · rfl
  refine ⟨t, z 1, ht, key _ (hb 1).symm, key _ (by simp [hb 1]), ?_⟩
  rw [← ez]
  exact isFreeGen_dForm z b hb



end GlobalTheory.FieldPair.Model

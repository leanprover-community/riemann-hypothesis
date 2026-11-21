import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBounds
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint

section
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
end

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  atlas_forward_decl GlobalTheory.FGDepth.detDepth_eq_zero_of_lt
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_zero_boundAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  intro E _ _ _ H Dw l Xo c p _ la f k
  letI := H.starRing
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hB : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      0 ≤ nuFacC Ch X f k ∧ nuFacC Ch X f k ≤ ((boundAll p (rk f) k : ℝ) : EReal) ∧ (k < p → nuFacC Ch X f k = 0) := by
    intro T io y Ch X
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine ⟨h1.1, ?_, fun hk => GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f) hk⟩
    have h2 := h1.2.2
    unfold boundAll
    exact h2
  have hmain : ∀ B : ℝ, (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p), nuFacC Ch X f k ≤ (B : EReal)) → FacBetween Xo la f k 0 B := by
    intro B hb T io e ho y
    refine ⟨?_, fun _ => ?_⟩
    · rw [EReal.coe_zero]
      exact le_nuFac fun Ch X => (hB T io y Ch X).1
    · obtain ⟨Ch⟩ := hch T io y
      obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
      exact (nuFac_le Ch X f k).trans (hb T io y Ch X)
  refine ⟨hmain _ fun T io y Ch X => (hB T io y Ch X).2.1, fun hk => hmain 0 fun T io y Ch X => ?_⟩
  rw [(hB T io y Ch X).2.2 hk, EReal.coe_zero]

end GlobalTheory.RefSum
end

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorDepth_between_zero_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  atlas_forward_decl GlobalTheory.RefSum.facBetween_zero_boundAll
end

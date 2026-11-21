import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (P : Ideal (MRing ι)) (D : ℕ) (a : K → ℤ),
    IsArithVar P (D + 1) → NefOnGenericDeg P a →
    ∃ m : ℕ, ∀ n i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))))
        ((n : ℤ) • a + fun _ => (m : ℤ)) i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def EulerHilbert.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Q : Ideal (MRingOver F ι)) (p : MvPolynomial K ℚ) (a₀ : ℕ),
    NumbersDVR.IsMultiProjPrime Q →
    (∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      (hilbFn Q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p) →
    ∀ b : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart F Q) b i)) →
      (Module.finrank F (KH.cechHc ι (KH.quotPart F Q) b 0) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p

theorem ringKrullDim_point :
    ringKrullDim (MRingOver ℚ pointIdx ⧸ (⊥ : Ideal (MRingOver ℚ pointIdx))) =
      ((0 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem cechHc_point_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver ℚ pointIdx) M] [Module ℚ M]
    [IsScalarTower ℚ (MRingOver ℚ pointIdx) M] (𝓜 : (Unit → ℤ) → Submodule ℚ M) (b : Unit → ℤ) (i : ℕ)
    (hi : 1 ≤ i) : Subsingleton (KH.cechHc pointIdx 𝓜 b i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have := cell_succ_isEmpty (K := Unit) (ι := pointIdx) n
  have : Subsingleton (KH.CechC ℚ pointIdx M (n + 1)) :=
    ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem EulerHilbert.hyps_inhabited :
    ∃ (p : MvPolynomial Unit ℚ) (a₀ : ℕ), NumbersDVR.IsMultiProjPrime (⊥ : Ideal (MRingOver ℚ pointIdx)) ∧
      (∀ a : Unit → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn (⊥ : Ideal (MRingOver ℚ pointIdx)) (fun k => (a k : ℤ)) : ℚ) =
          MvPolynomial.eval (fun k => (a k : ℚ)) p) ∧
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc pointIdx (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ pointIdx))) 0 i) := by
  obtain ⟨p, a₀, -, hp⟩ := MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ Unit pointIdx ⊥ 0
    NumbersDVR.isMultiProjPrime_bot ringKrullDim_point
  exact ⟨p, a₀, NumbersDVR.isMultiProjPrime_bot, hp, fun i hi => cechHc_point_subsingleton _ _ i hi⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem NefShiftPolynomial.proof (hF : FujitaGeneric.Statement) (hC : ChartLatQCech.Statement)
    (hE : EulerHilbert.Statement) (hL : EventualPolyLine.Statement) : NefShiftPolynomial.Statement := by
  intro K _ ι _ Ω _ _ y D a _ hV _ hN
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨hQ, hdim⟩ := ShiftDegreePolynomial.genericFibre hV
  set Q := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hQdef
  obtain ⟨m, hm⟩ := hF K ι (mCoordIdeal y) D a hV hN
  obtain ⟨p, a₀, hpdeg, hp⟩ :=
    MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ K ι Q D hQ hdim
  obtain ⟨r, hrdeg, hrcoef, hr⟩ := hL K D (hilbFn Q) p a₀ a (fun _ => (m : ℤ)) hpdeg hp
  refine ⟨m, r, hrdeg, ?_, Eventually.of_forall fun n => ?_⟩
  · have hH : ∀ i j : DecidableEq K, @hilbFn K i ι ℚ _ Q = @hilbFn K j ι ℚ _ Q := fun i j => by
      rw [Subsingleton.elim i j]
    have hg : genDeg (mCoordIdeal y) D a = eventualValue (mixedDiff (fun _ : Fin D => a) (hilbFn Q)) :=
      congrArg (fun h => eventualValue (mixedDiff (fun _ : Fin D => a) h)) (hH _ _)
    rw [hrcoef, hg]
  · obtain ⟨e⟩ := hC K ι Ω y (D + 1) ((n : ℤ) • a + fun _ => (m : ℤ)) hV
    rw [e.finrank_eq, ← hr n, ← hE ℚ K ι Q p a₀ hQ hp _ (hm n)]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

theorem exists_hilbert_le_O (hR : RayField) (B : Base) (δ : FieldDat B.toPre) (hδ : δ.ray ≤ B.KsC) :
    ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn B.host.φ₀ ⊤ M ∧
      ∀ z ∈ M, IsIntegral ℤ z → ∃ y : B.O, B.embLL (B.OtoLL y) = z := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn B.host.φ₀ hR (𝔮 := ⊤) top_ne_bot
  refine ⟨M, hM, fun z hz hI => ?_⟩
  have hle : M ≤ δ.ray := RayMono.le_of_isRayFieldIn_of_dvd _ _ _ _ _ _ (natIdeal_ne_bot (modulus_ne_zero B.toPre))
    (Ideal.dvd_iff_le.2 le_top) hM δ.isRay
  obtain ⟨x, hx, rfl⟩ := B.mem_KsC.1 (hδ (hle hz))
  have hx' : IsIntegral ℤ x :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hI
  obtain ⟨y, hy⟩ := B.O_full x hx hx'
  exact ⟨y, by rw [hy]⟩

theorem twistConductor_not_over_levelPrimes (B : Base) (T : TwDat B) (w : B.places.Pl) {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : v ∈ T.Q w)
    (u : B.Word) (hp : (B.T u).Prime) : ¬ OverP B.host (B.T u) v := by
  intro ho
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  have := Examples₂.PlacesToy.prime_mem_unique v h1 hp (Ideal.absNorm_mem _) ho
  exact h2 (this ▸ .inr (.inr (.inr (.inr (.inl ⟨u, rfl⟩)))))

end GlobalTheory.Mem.HD
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
end

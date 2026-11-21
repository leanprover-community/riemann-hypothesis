import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
import ReciprocityTheory.ReductiveGroups.LocalHeights.Imports

section
open Formalism.BasicNotions

namespace Formalism.L2

def LocsCoverTwF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i)


theorem locsCoverTwF_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M), HeckeStdTw T.B) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨M, T, hT⟩ := hx0 x hx i
  exact locsCoverTw_of_tie T hT

end Formalism.L2
end

section
open Formalism.BasicNotions

namespace Formalism.L2


theorem linkEtaTw_of_plain {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hP : HeckeStdPlain)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := h
  refine locsCoverTwF_of Fm ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hex⟩ := hx x hx' i
  exact ⟨M, T, heckeStd_of_plain T hP HT hex (genOutBad_of T)⟩



end Formalism.L2
end

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

section Rfl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end Rfl

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam


end Formalism.L2
end
end

section
open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_main {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ ∀ z : (Fm.D x i).host.E, (Fm.D x i).host.conj z = IsCMField.complexConj _ z) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_of_statement Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hstar⟩ := hx x hx' i
  exact ⟨M, T, HT, splitEx_of_star hstar⟩



end Formalism.L2
end

section
open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

namespace Formalism.L2

theorem hostConj_eq_restrict (D : D7) :
    D.host.conj = (IsCMField.complexConj D.host.E).restrictScalars ℚ := by
  symm
  refine (D.host.toHostAx.eq_conjE_iff _).mpr ?_
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  exact (D.host.isConj_iff_galE φ _).mp
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E φ x)

theorem hostConj_eq_complexConj (D : D7) :
    ∀ z : D.host.E, D.host.conj z = IsCMField.complexConj D.host.E z := by
  intro z
  rw [hostConj_eq_restrict D]
  rfl

theorem locs_cover_twists_of_hecke {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_main Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT⟩ := hx x hx' i
  exact ⟨M, T, HT, hostConj_eq_complexConj (Fm.D x i)⟩



example (D : D7) (z : D.host.E) :
    letI : IsCMField D.host.E := hostCM D.host
    D.host.conj z = IsCMField.complexConj D.host.E z :=
  hostConj_eq_complexConj D z

example (K : Type) [Field K] [NumberField K] (i₁ i₂ : IsCMField K) : i₁ = i₂ := rfl

end Formalism.L2
end

section
open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i) :=
  locs_cover_twists_of_hecke Fm ReciprocityTheory.ChartRestriction.L3H.heckeStd hfam

theorem linkEta_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    Formalism.MainNotions.LinkEta Fm := by
  exact linkEtaTw_closed Fm hfam


end Formalism.L2
end

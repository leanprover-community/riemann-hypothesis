import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.HodgeTateFromSandwich
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PhiMain
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.admitted
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CharZeroBdR

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def SeamAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Good D ∧ D.Span Model.Good (Bst l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

theorem smooth_of (h1 : PeriodRingFacts) (h2 : BcrisRegularPeriodRing) (h3 : ComparisonPairing) (h4 : ComparisonInjectiveStrict) (h5 : ComparisonAdmissible) (h6 : EtaleSideSmoothAndSemistable)
    (hI : ZIn) (hS : SeamS) : SmoothModelCrystalline ∧ DeRhamComparisonSmooth := by
  constructor
  · intro l _ K _ M hM hs n a b
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hS l K
    obtain ⟨P, hP⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).1 hL e β κ
    exact h5 l K _ _ P _ (h2 l K) M ⟨hM, hs⟩ n (h4 l K _ _ P (h1 l K) (h6 hI l K).1 M ⟨hM, hs⟩ n).1
      (hP _ _ (t_inv_mem l) (h2 l K).q_mem hsp M ⟨hM, hs⟩ ⟨hM, hs⟩ n) a b
  · intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hS l K
    obtain ⟨P, -⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).1 hL e β κ
    exact ⟨P.cmp (h6 hI l K).1 (h4 l K _ _ P (h1 l K) (h6 hI l K).1)⟩



end CrystallineSemistableComparison
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

theorem zIn (h : FormalIn) (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : ZIn :=
  ⟨h.a6nat, h.a6ring, h.a9, h.et.a11, h4, h8, bock h, root h, sum h⟩

theorem etSide : EtaleSideSmoothAndSemistable := fun h l _ K _ =>
  ⟨adic h l K _ (fun _ hM => hM.1) (comp l K).1 fun M hM => geo l K M hM.1,
    adic h l K _ (fun _ hM => hM) (comp l K).2 fun M hM => geo l K M hM⟩

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi


end CrystallineSemistableComparison
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

def EtSideS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K))

theorem cstSmooth_of_etSide (gL : GlueL) (gE : GlueE) (gB : GlueB) (hC : BcrisPeriodFacts) (hX : ResEx)
    (hI : EtSideS) (h : Chapters) : CstSmooth := by
  have hS : SeamS := by
    intro l _ K _
    obtain ⟨Amp, h1, h2, h3, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨r⟩ := hX l K
    obtain ⟨F⟩ := h4 r
    refine ⟨dat Amp, ⟨gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2, gE l K Amp (h.et l K), ⟨β⟩, h3⟩, ?_⟩
    rw [← e] at F
    have := fac l K _ _ _ _ _ β β₁ F
    rwa [(hC l K r).2] at this
  refine ⟨?_, ?_, ?_⟩
  · intro l _ K _ M hM hs n a b
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hS l K
    obtain ⟨P, hP⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact adm l K _ _ P _ (regCr l K) M ⟨hM, hs⟩ n (inj l K _ _ P (facts l K) (hI l K) M ⟨hM, hs⟩ n).1
      (hP _ _ (t_inv_mem l) (regCr l K).q_mem hsp M ⟨hM, hs⟩ ⟨hM, hs⟩ n) a b
  · intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hS l K
    obtain ⟨P, -⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact ⟨P.cmp (hI l K) (inj l K _ _ P (facts l K) (hI l K))⟩
  · intro l _ K _ r
    obtain ⟨Amp, h1, h2, ⟨κ⟩, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨F⟩ := h4 r
    obtain ⟨ε⟩ := gE l K Amp (h.et l K)
    rw [← e] at F
    exact phi l K _ _ _ _ _ (facts l K) (hC l K r).1 (hI l K) (gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2) ε β β₁ κ F

end CrystallineSemistableComparison
end
end

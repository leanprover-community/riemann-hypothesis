import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombination
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertibleStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel

namespace GlobalTheory.LatPresc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem latV_eq_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) = latV S L' (· = v) :=
  le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLat_congr {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    {L L' : Lat S} (h : latV S L (· = p.v) = latV S L' (· = p.v)) (Λ : Submodule 𝒪[k] (n → k)) :
    β.IsLat L Λ ↔ β.IsLat L' Λ := by
  unfold Frame.IsLat
  rw [h]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i ∈ l, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k (p i) S n (β i) M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩
    · by_cases e : i' = i
      · subst e; exact h3
      · have hne : (p i').v ≠ (p i).v := fun e' => e (hp e')
        exact (isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2
          (h1 i' ((List.mem_cons.1 hi').resolve_left e))
    · exact (latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans
        (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))

theorem latAll : ∀ D : D7, LatAll D := by
  intro D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ
  obtain ⟨M, hM, h1, h2⟩ := exists_modify hP.inj α Λ hΛ hL I
  exact ⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩

end GlobalTheory.LatPresc
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces : ∀ D : D7, GlobalTheory.FinPl.LatAll D := by
  atlas_forward_decl GlobalTheory.LatPresc.latAll
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RebaseProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section One

variable {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : Frame p S n'} {β : Frame p T n}

theorem cc (hstd : IsStdChar D ψ (-1)) (hu : p.UnitAA) {NS NS' : Lat S} {NT NT' : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S NS') (h4 : IsSelfDualC T NT')
    {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)} (hS : α.IsLat NS ΛS) (hS' : α.IsLat NS' ΛS)
    (hT : β.IsLat NT ΛT) (hT' : β.IsLat NT' ΛT) {f : WO S T → ℂ} (hf : Vac ψ S T NS NT (· = p.v) f) :
    Vac ψ S T NS' NT' (· = p.v) f ∧ ∀ Ψ h, Over ψ α β NS NT f Ψ h → Over ψ α β NS' NT' f Ψ h := by
  have hb := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f hf).2.2 hu ΛS ΛT hS hT
  exact (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS NS' NT NT' h1 h2 h3 h4).1 ΛS ΛT hS' hT' f f hb

theorem sp1 (hstd : IsStdChar D ψ (-1)) (hu : p.UnitAA) {NS N'S : Lat S} {NT N'T : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S N'S) (h4 : IsSelfDualC T N'T)
    {AS A'S : Submodule 𝒪[k] (n' → k)} {AT A'T : Submodule 𝒪[k] (n → k)} [AS.IsLattice k] [AT.IsLattice k]
    (hAS : α.IsLat NS AS) (hAT : β.IsLat NT AT) (hA'S : α.IsLat N'S A'S) (hA'T : β.IsLat N'T A'T)
    {f₀ g : WO S T → ℂ} (hf₀ : Vac ψ S T NS NT (· = p.v) f₀) (hg : Over ψ α β NS NT f₀ (latInd A'S A'T) g) :
    Vac ψ S T N'S N'T (· = p.v) g ∧ ∀ Ψ h, Over ψ α β NS NT f₀ Ψ h ↔ Over ψ α β N'S N'T g Ψ h := by
  have R := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β NS N'S NT N'T h1 h2 h3 h4).1 A'S A'T hA'S hA'T f₀ g hg
  refine ⟨R.1, fun Ψ h => ⟨R.2 Ψ h, fun hh => ?_⟩⟩
  obtain ⟨g', hg', huniq⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β N'S N'T h3 h4 g R.1).1 (latInd AS AT)
    (latInd_mem_SB AS AT)
  have R' := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hstd hu S T α β N'S NS N'T NT h3 h4 h1 h2).1 AS AT hAS hAT g g' hg'
  have hself := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hstd S T α β NS NT h1 h2 f₀ hf₀).2.2 hu AS AT hAS hAT
  have he : f₀ = g' := huniq f₀ (R.2 _ _ hself)
  rw [he]
  exact R'.2 Ψ h hh

end One

section Chain

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}

theorem overAll_congrΨ {LS : Lat S} {LT : Lat T} {Ψ Ψ' : ι → Matrix n n' k → ℂ} (l : List ι)
    (h : ∀ j ∈ l, Ψ j = Ψ' j) : ∀ f f', OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β LS LT Ψ' l f f' := by
  induction l with
  | nil => intro f f' hf; exact hf
  | cons i l ih =>
    intro f f' hf
    obtain ⟨g, hg, hO⟩ := ValDbl.overAll_cons.1 hf
    refine ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) f g hg, ?_⟩
    rw [← h i List.mem_cons_self]
    exact hO

theorem overAll_congr (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) {NS NS' : Lat S} {NT NT' : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) (h3 : IsSelfDualC S NS') (h4 : IsSelfDualC T NT')
    {Ψ : ι → Matrix n n' k → ℂ} (l : List ι)
    (hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat NS ΛS ∧ (α j).IsLat NS' ΛS ∧ (β j).IsLat NT ΛT ∧ (β j).IsLat NT' ΛT) :
    ∀ f f', OverAll ψ α β NS NT Ψ l f f' → OverAll ψ α β NS' NT' Ψ l f f' := by
  induction l with
  | nil => intro f f' hf; exact hf
  | cons i l ih =>
    intro f f' hf
    obtain ⟨g, hg, hO⟩ := ValDbl.overAll_cons.1 hf
    obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame i List.mem_cons_self
    exact ValDbl.overAll_cons.2 ⟨g, ih (fun j hj => hsame j (List.mem_cons_of_mem _ hj)) f g hg,
      (cc hstd (hunit i) h1 h2 h3 h4 a b c d hO.2.2.1).2 _ _ hO⟩

theorem overAll_self (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) {NS : Lat S} {NT : Lat T}
    (h1 : IsSelfDualC S NS) (h2 : IsSelfDualC T NT) {AS : ι → Submodule 𝒪[k] (n' → k)}
    {AT : ι → Submodule 𝒪[k] (n → k)} (hA : ∀ j, (α j).IsLat NS (AS j) ∧ (β j).IsLat NT (AT j)) (f : WO S T → ℂ)
    (l : List ι) (hf : ∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) f) :
    OverAll ψ α β NS NT (fun j => latInd (AS j) (AT j)) l f f := by
  induction l with
  | nil => exact ValDbl.overAll_nil.2 rfl
  | cons i l ih =>
    exact ValDbl.overAll_cons.2 ⟨f, ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)),
      (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hstd S T (α i) (β i) NS NT h1 h2 f (hf i List.mem_cons_self)).2.2 (hunit i)
        (AS i) (AT i) (hA i).1 (hA i).2⟩

variable {NS : Lat S} {NT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem swap_fwd (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (i : ι) (l : List ι) (hil : i ∉ l) (b : WO S T → ℂ) (hb : Vac ψ S T NS NT (· = (p i).v) b) :
    ∀ f', (∃ h, OverAll ψ α β NS NT Ψ l b h ∧ Over ψ (α i) (β i) NS NT h (Ψ i) f') →
      ∃ k', Over ψ (α i) (β i) NS NT b (Ψ i) k' ∧ OverAll ψ α β NS NT Ψ l k' f' := by
  induction l with
  | nil =>
    rintro f' ⟨h, hh, hO⟩
    rw [ValDbl.overAll_nil.1 hh] at hO
    exact ⟨f', hO, ValDbl.overAll_nil.2 rfl⟩
  | cons j l ih =>
    rintro f' ⟨h, hh, hO⟩
    have hij : i ≠ j := fun e => hil (e ▸ List.mem_cons_self)
    have hil' : i ∉ l := fun h' => hil (List.mem_cons_of_mem _ h')
    obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 hh
    have hmv := ValDbl.overAll_vac hstd hinj l b m hm i hil' hb
    obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p j) (p i) n n' n n' ψ hstd (hunit j) (hunit i)
      (fun e => hij (hinj e.symm)) S T (α j) (β j) (α i) (β i) NS NT m h f' (Ψ j) (Ψ i) hmv hmO hO
    obtain ⟨k', hk', hl⟩ := ih hil' g' ⟨m, hm, hg'1⟩
    exact ⟨k', hk', ValDbl.overAll_cons.2 ⟨g', hl, hg'2⟩⟩

theorem swap_bwd (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (i : ι) (l : List ι) (hnd : l.Nodup) (hil : i ∉ l) (b : WO S T → ℂ)
    (hb : ∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) b) :
    ∀ f', (∃ k', Over ψ (α i) (β i) NS NT b (Ψ i) k' ∧ OverAll ψ α β NS NT Ψ l k' f') →
      ∃ h, OverAll ψ α β NS NT Ψ l b h ∧ Over ψ (α i) (β i) NS NT h (Ψ i) f' := by
  induction l with
  | nil =>
    rintro f' ⟨k', hk', hl⟩
    rw [ValDbl.overAll_nil.1 hl]
    exact ⟨b, ValDbl.overAll_nil.2 rfl, hk'⟩
  | cons j l ih =>
    rintro f' ⟨k', hk', hl⟩
    rw [List.nodup_cons] at hnd
    have hij : i ≠ j := fun e => hil (e ▸ List.mem_cons_self)
    have hil' : i ∉ l := fun h' => hil (List.mem_cons_of_mem _ h')
    obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 hl
    obtain ⟨h₀, hh₀, hO₀⟩ := ih hnd.2 hil' (fun j' hj' => hb j' (List.mem_cons_of_mem _ hj')) m ⟨k', hk', hm⟩
    have hv := ValDbl.overAll_vac hstd hinj l b h₀ hh₀ j hnd.1 (hb j List.mem_cons_self)
    obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j)
      (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) NS NT h₀ m f' (Ψ i) (Ψ j) hv hO₀ hmO
    exact ⟨g', ValDbl.overAll_cons.2 ⟨h₀, hh₀, hg'1⟩, hg'2⟩

end Chain

section Front

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
  {Ψ : ι → Matrix n n' k → ℂ}

theorem front (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    {N₁S N'S : Lat S} {N₁T N'T : Lat T} (h1 : IsSelfDualC S N₁S) (h2 : IsSelfDualC T N₁T) (h3 : IsSelfDualC S N'S)
    (h4 : IsSelfDualC T N'T) (i : ι) (l : List ι) (hnd : l.Nodup) (hil : i ∉ l)
    {AS A'S : Submodule 𝒪[k] (n' → k)} {AT A'T : Submodule 𝒪[k] (n → k)} [AS.IsLattice k] [AT.IsLattice k]
    (hAS : (α i).IsLat N₁S AS) (hAT : (β i).IsLat N₁T AT) (hA'S : (α i).IsLat N'S A'S) (hA'T : (β i).IsLat N'T A'T)
    (hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat N₁S ΛS ∧ (α j).IsLat N'S ΛS ∧ (β j).IsLat N₁T ΛT ∧ (β j).IsLat N'T ΛT)
    {g₁ g : WO S T → ℂ} (hg₁i : Vac ψ S T N₁S N₁T (· = (p i).v) g₁)
    (hg₁ : ∀ j ∈ l, Vac ψ S T N₁S N₁T (· = (p j).v) g₁) (hg : ∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g)
    (hO : Over ψ (α i) (β i) N₁S N₁T g₁ (latInd A'S A'T) g) :
    ∀ f', OverAll ψ α β N₁S N₁T Ψ (i :: l) g₁ f' ↔ OverAll ψ α β N'S N'T Ψ (i :: l) g f' := by
  have hsp := sp1 hstd (hunit i) h1 h2 h3 h4 hAS hAT hA'S hA'T hg₁i hO
  have hsame' : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
      (α j).IsLat N'S ΛS ∧ (α j).IsLat N₁S ΛS ∧ (β j).IsLat N'T ΛT ∧ (β j).IsLat N₁T ΛT := fun j hj => by
    obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame j hj
    exact ⟨ΛS, ΛT, b, a, d, c⟩
  intro f'
  constructor
  · intro hL
    obtain ⟨k', hk', hl⟩ := swap_fwd hstd hunit hinj i l hil g₁ hg₁i f' (ValDbl.overAll_cons.1 hL)
    exact ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g hg f'
      ⟨k', (hsp.2 _ _).1 hk', overAll_congr hstd hunit h1 h2 h3 h4 l hsame k' f' hl⟩)
  · intro hR
    obtain ⟨k', hk', hl⟩ := swap_fwd hstd hunit hinj i l hil g hsp.1 f' (ValDbl.overAll_cons.1 hR)
    exact ValDbl.overAll_cons.2 (swap_bwd hstd hunit hinj i l hnd hil g₁ hg₁ f'
      ⟨k', (hsp.2 _ _).2 hk', overAll_congr hstd hunit h3 h4 h1 h2 l hsame' k' f' hl⟩)

end Front

section Gen

variable {ι : Type} {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}

open Classical in

theorem gen (hstd : IsStdChar D ψ (-1)) {I : List ι} {P : Pl D → Prop} (hPl : Places p I P) (l : List ι) :
    l.Nodup → ∀ (NS N'S : Lat S) (NT N'T : Lat T) (AS A'S : ι → Submodule 𝒪[k] (n' → k))
      (AT A'T : ι → Submodule 𝒪[k] (n → k)),
    IsSelfDualC S NS → IsSelfDualC T NT → IsSelfDualC S N'S → IsSelfDualC T N'T →
    (∀ j, (AS j).IsLattice k ∧ (A'S j).IsLattice k ∧ (AT j).IsLattice k ∧ (A'T j).IsLattice k) →
    (∀ j, (α j).IsLat NS (AS j) ∧ (α j).IsLat N'S (A'S j) ∧ (β j).IsLat NT (AT j) ∧ (β j).IsLat N'T (A'T j)) →
    (∀ j, j ∉ l → A'S j = AS j ∧ A'T j = AT j) →
    ∀ f g, (∀ j ∈ l, Vac ψ S T NS NT (· = (p j).v) f) →
      OverAll ψ α β NS NT (fun j => latInd (A'S j) (A'T j)) l f g →
      (∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g) ∧
        ∀ Ψ f', OverAll ψ α β NS NT Ψ l f f' ↔ OverAll ψ α β N'S N'T Ψ l g f' := by
  have hunit := hPl.unit
  have hinj := hPl.inj
  induction l with
  | nil =>
    intro _ NS N'S NT N'T AS A'S AT A'T _ _ _ _ _ _ _ f g _ hg
    rw [ValDbl.overAll_nil.1 hg]
    exact ⟨fun j hj => by simp at hj, fun Ψ f' => Iff.rfl⟩
  | cons i l ih =>
    intro hl NS N'S NT N'T AS A'S AT A'T h1 h2 h3 h4 hL hA hout f g hf hg
    rw [List.nodup_cons] at hl
    obtain ⟨hil, hnd⟩ := hl
    let BS : ι → Submodule 𝒪[k] (n' → k) := fun j => if j ∈ l then A'S j else AS j
    let BT : ι → Submodule 𝒪[k] (n → k) := fun j => if j ∈ l then A'T j else AT j
    have hBS : ∀ j, (BS j).IsLattice k := fun j => by
      by_cases hj : j ∈ l
      · simp only [BS, if_pos hj]; exact (hL j).2.1
      · simp only [BS, if_neg hj]; exact (hL j).1
    have hBT : ∀ j, (BT j).IsLattice k := fun j => by
      by_cases hj : j ∈ l
      · simp only [BT, if_pos hj]; exact (hL j).2.2.2
      · simp only [BT, if_neg hj]; exact (hL j).2.2.1
    obtain ⟨N₁S, hN₁S, hlatS, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n' S α NS h1 BS hBS
    obtain ⟨N₁T, hN₁T, hlatT, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι p I P hPl n T β NT h2 BT hBT
    obtain ⟨g₁, hg₁, hO⟩ := ValDbl.overAll_cons.1 hg
    have hg₁' : OverAll ψ α β NS NT (fun j => latInd (BS j) (BT j)) l f g₁ :=
      overAll_congrΨ l (fun j hj => by simp only [BS, BT, if_pos hj]) f g₁ hg₁
    have IH := ih hnd NS N₁S NT N₁T AS BS AT BT h1 h2 hN₁S hN₁T
      (fun j => ⟨(hL j).1, hBS j, (hL j).2.2.1, hBT j⟩) (fun j => ⟨(hA j).1, hlatS j, (hA j).2.2.1, hlatT j⟩)
      (fun j hj => ⟨by simp only [BS, if_neg hj], by simp only [BT, if_neg hj]⟩)
      f g₁ (fun j hj => hf j (List.mem_cons_of_mem _ hj)) hg₁'
    have hBi : BS i = AS i ∧ BT i = AT i := ⟨by simp only [BS, if_neg hil], by simp only [BT, if_neg hil]⟩
    have hN₁Si : (α i).IsLat N₁S (AS i) := hBi.1 ▸ hlatS i
    have hN₁Ti : (β i).IsLat N₁T (AT i) := hBi.2 ▸ hlatT i
    have hg₁v : Vac ψ S T NS NT (· = (p i).v) g₁ :=
      ValDbl.overAll_vac hstd hinj l f g₁ hg₁ i hil (hf i List.mem_cons_self)
    have C := cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hg₁v
    have hO₁ := C.2 _ _ hO
    have hsame : ∀ j ∈ l, ∃ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)),
        (α j).IsLat N₁S ΛS ∧ (α j).IsLat N'S ΛS ∧ (β j).IsLat N₁T ΛT ∧ (β j).IsLat N'T ΛT := fun j hj =>
      ⟨A'S j, A'T j, by simpa only [BS, if_pos hj] using hlatS j, (hA j).2.1,
        by simpa only [BT, if_pos hj] using hlatT j, (hA j).2.2.2⟩
    have hgv : ∀ j ∈ l, Vac ψ S T N'S N'T (· = (p j).v) g := fun j hj => by
      obtain ⟨ΛS, ΛT, a, b, c, d⟩ := hsame j hj
      have hji : (p j).v ≠ (p i).v := fun e => hil (by rw [← hinj e]; exact hj)
      have hk := (ValDbl.over_keep hstd hO₁).2 (p j).v hji (IH.1 j hj)
      exact (cc hstd (hunit j) hN₁S hN₁T h3 h4 a b c d hk).1
    haveI := (hL i).1
    haveI := (hL i).2.2.1
    have hsp := sp1 hstd (hunit i) hN₁S hN₁T h3 h4 hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2 C.1 hO₁
    refine ⟨fun j hj => ?_, fun Ψ f' => ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj'
      · exact hsp.1
      · exact hgv j hj'
    · rw [← front hstd hunit hinj hN₁S hN₁T h3 h4 i l hnd hil hN₁Si hN₁Ti (hA i).2.1 (hA i).2.2.2
        hsame C.1 IH.1 hgv hO₁ f']
      constructor
      · intro h
        obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 h
        exact ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).1 hm,
          (cc hstd (hunit i) h1 h2 hN₁S hN₁T (hA i).1 hN₁Si (hA i).2.2.1 hN₁Ti hmO.2.2.1).2 _ _ hmO⟩
      · intro h
        obtain ⟨m, hm, hmO⟩ := ValDbl.overAll_cons.1 h
        exact ValDbl.overAll_cons.2 ⟨m, (IH.2 Ψ m).2 hm,
          (cc hstd (hunit i) hN₁S hN₁T h1 h2 hN₁Si (hA i).1 hN₁Ti (hA i).2.2.1 hmO.2.2.1).2 _ _ hmO⟩

end Gen

theorem rebaseAll : ∀ D : D7, RebaseAll D := by
  intro D
  unfold RebaseAll
  intro k _ _ _ _ ι p I P hPl n n' _ _ _ _ ψ hstd S T α β LS MS LT MT hLS hLT hMS hMT
  choose ALS hALS1 hALS2 _hALS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 LS hLS
  choose AMS hAMS1 hAMS2 _hAMS3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n' (α i)).2.2.2.1 MS hMS
  choose ALT hALT1 hALT2 _hALT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 LT hLT
  choose AMT hAMT1 hAMT2 _hAMT3 using fun i => (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) T n (β i)).2.2.2.1 MT hMT
  have hL : ∀ j, (ALS j).IsLattice k ∧ (AMS j).IsLattice k ∧ (ALT j).IsLattice k ∧ (AMT j).IsLattice k :=
    fun j => ⟨hALS1 j, hAMS1 j, hALT1 j, hAMT1 j⟩
  have hA : ∀ j, (α j).IsLat LS (ALS j) ∧ (α j).IsLat MS (AMS j) ∧ (β j).IsLat LT (ALT j) ∧ (β j).IsLat MT (AMT j) :=
    fun j => ⟨hALS2 j, hAMS2 j, hALT2 j, hAMT2 j⟩
  obtain ⟨e, he1, he2⟩ := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β LS LT hLS hLT
    (fun i => latInd (AMS i) (AMT i))).1 (fun i => by haveI := hAMS1 i; haveI := hAMT1 i; exact latInd_mem_SB _ _)
  have AC' := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hPl n n' ψ hstd S T α β MS MT hMS hMT (fun i => latInd (ALS i) (ALT i))
  obtain ⟨e', he'1, he'2⟩ := AC'.1 (fun i => by haveI := hALS1 i; haveI := hALT1 i; exact latInd_mem_SB _ _)
  refine ⟨e, e', he1, he'1, fun f hf => ?_⟩
  have hfv : ∀ j, Vac ψ S T LS LT (· = (p j).v) f := fun j => ValDbl.vac_at ((hPl.mem _).2 ⟨j, rfl⟩) hf
  obtain ⟨hgv, hiff⟩ := gen hstd hPl I hPl.nodup LS MS LT MT ALS AMS ALT AMT hLS hLT hMS hMT hL hA
    (fun j hj => absurd (hPl.all j) hj) f (comb ψ S T e f) (fun j _ => hfv j) (he2 f hf)
  have hth : IsThetaFunO ψ S T (comb ψ S T e f) := ValDbl.overAll_theta hstd I f _ (he2 f hf) hf.1
  have hgV : Vac ψ S T MS MT P (comb ψ S T e f) := ⟨hth, GlobalTheory.VacLoc.latVac_of_places ψ S T MS MT P _ hth
    fun v hv => by obtain ⟨j, rfl⟩ := (hPl.mem v).1 hv; exact hgv j (hPl.all j)⟩
  refine ⟨hgV, ?_, hiff⟩
  have hs := (hiff _ f).1 (overAll_self hstd hPl.unit hLS hLT (fun j => ⟨(hA j).1, (hA j).2.2.1⟩) f I
    fun j _ => hfv j)
  exact AC'.2.1 _ _ _ (he'2 _ hgV) hs

end GlobalTheory.FinPl.RebaseProof
end
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumChangeAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.RebaseAll D := by
  atlas_forward_decl GlobalTheory.FinPl.RebaseProof.rebaseAll
end

section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractionOfVacuumCombinations_proof : ∀ D : D7, GlobalTheory.FinPl.ContrOp D := by
  first | exact @GlobalTheory.FinPl.ContrOpProof.contrOp | exact GlobalTheory.FinPl.ContrOpProof.contrOp | (intros; apply GlobalTheory.FinPl.ContrOpProof.contrOp <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd InDual mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
open GlobalTheory.FinPl.Vertex

namespace GlobalTheory.FinPl.VertexExactCount

section Count

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem card_withLat_smul (g : GL n k) (L : Submodule 𝒪[k] (n → k)) :
    (withLat (g • L)).card = (withLat L).card := by
  refine Finset.card_bij (fun P _ => g⁻¹ • P) ?_ ?_ ?_
  · intro P hP
    rw [mem_withLat] at hP ⊢
    rw [Pair.smul_lat, hP, inv_smul_smul]
  · intro P _ P' _ h
    exact MulAction.injective g⁻¹ h
  · intro P hP
    refine ⟨g • P, ?_, inv_smul_smul g P⟩
    rw [mem_withLat] at hP ⊢
    rw [Pair.smul_lat, hP]

theorem card_withLat_eq (Q Q₀ : Pair k n) : (withLat Q.lat).card = (withLat Q₀.lat).card := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [← hg, Pair.smul_lat, card_withLat_smul]

theorem card_withLat_pos (Q : Pair k n) : 0 < (withLat Q.lat).card :=
  Finset.card_pos.2 ⟨Q, mem_withLat.2 rfl⟩

open Classical in

def pairCount (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] : ℕ :=
  if h : Nonempty (Pair k n) then (withLat h.some.lat).card else 1

theorem pairCount_pos : 0 < pairCount k n := by
  unfold pairCount
  split_ifs with h
  · exact card_withLat_pos _
  · exact one_pos

theorem card_withLat_eq_pairCount (Q : Pair k n) : (withLat Q.lat).card = pairCount k n := by
  unfold pairCount
  rw [dif_pos ⟨Q⟩]
  exact card_withLat_eq _ _

end Count

end GlobalTheory.FinPl.VertexExactCount

namespace GlobalTheory.FinPl.VertexExactCount

open Classical in

theorem vertexExact (D : D7) : VertexExact D := by
  intro k _ _ _ _ p q ψ χ hχ hIs
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  obtain ⟨e, he, HC⟩ := GlobalTheory.T.splitPlace_lineComponents_contraction D k p ψ χ hIs
  obtain ⟨ν, hν, -⟩ := exists_isUnitVol k
  let ε : 𝓀[k]ˣ := if e = 1 then 1 else -1
  have hεe : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1) := by
    by_cases h1 : e = 1
    · exact Or.inl ⟨h1, if_pos h1⟩
    · exact Or.inr ⟨he.resolve_left h1, if_neg h1⟩
  refine ⟨ε, ?_, ?_⟩
  · rcases hεe with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  intro n n' n'' _ _ _ _ _ _
  obtain ⟨r₁, e₁, hr₁, HS⟩ := GlobalTheory.T.gluedPlaceSourceConstant_proof D k p n n' q χ hχ
  refine ⟨r₁ * (pairCount k n : ℝ), e₁, mul_pos hr₁ (Nat.cast_pos.2 pairCount_pos), ?_⟩
  intro P Q R σ B J B' s₁ s₂ l vL hu₁ hu₂ α α₀ β γ γ₀ hα hγ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' o₁ o₁' o₂ o₂' φ hφ
  have hψ : IsStdChar D ψ (-1) := s₁.weil₀.std
  have hχc : Continuous χ := by
    have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
    have h1 : Continuous fun a => psiE ψ (p.sec a) := hψ.1.1.comp (ht.comp p.cont_sec)
    have h2 : (fun a => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hIs
    refine continuous_induced_rng.2 ?_
    change Continuous (fun a => ((χ a : Circle) : ℂ))
    rw [h2]
    exact h1
  obtain ⟨lS₁, lT₁, uS₁, uT₁, lin₁⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ _ _ _ _ _ s₁.weil₀
  obtain ⟨lS₂, lT₂, uS₂, uT₂, lin₂⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ _ _ _ _ _ s₂.weil₀
  have vS₁ := uS₁ hu₁.2
  have vT₁ := uT₁ hu₁.1
  have vS₂ := uS₂ hu₂.2
  have vT₂ := uT₂ hu₂.1
  obtain ⟨-, D2, -⟩ := GlobalTheory.T.gluedLattice_finite_expansions_localField k n n'' q (resChar χ hχ q) (resChar_ne_one hχ q) Q.lat
  let μ : Measure (n → k) := Measure.pi fun _ => ν
  have I0 : fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) ≠ 0 := Comm.fpair_ne_zero χ hχc e he μ Q.lat
  have hvec := Comm.vecInd_mem Q.lat
  have hdual := Comm.dualInd_mem Q.lat
  let col : ∀ Ψ : Matrix n n' k → ℂ, Ψ ∈ SB (Matrix n n' k) → ∀ a : (n → k) → ℂ, a ∈ SB (n → k) →
      SB (Matrix n (n' ⊕ Fin 1) k) := fun Ψ hΨ a ha => ⟨tensCol Ψ a, Comm.tensCol_mem hΨ ha⟩
  let row : ∀ Ψ : Matrix n'' n k → ℂ, Ψ ∈ SB (Matrix n'' n k) → ∀ b : (n → k) → ℂ, b ∈ SB (n → k) →
      SB (Matrix (n'' ⊕ Fin 1) n k) := fun Ψ hΨ b hb => ⟨tensRow Ψ b, Comm.tensRow_mem hΨ hb⟩
  have one_emb : ∀ {S₀ A L : HSp D} (o : OrthDec S₀ A L), o.emb (1, 1) = 1 := fun o => map_one o.emb
  obtain ⟨U₁, a₁, b₁, t₁⟩ := overMap hψ o₁ fun Ψ f h => (lin₁ _ _ α₀ β L₁ L₂ f₁ Ψ f h).2.2
  obtain ⟨U₂, a₂, b₂, t₂⟩ := overMap hψ o₂ fun Ψ f h => (lin₂ _ _ β γ₀ L₂' L₃ f₂ Ψ f h).2.2
  obtain ⟨Θ, hΘ⟩ := exists_trilinear s₁ s₂ l vL U₁ U₂ t₁ t₂
  have key : ∀ (v : caSub B.A) (Ψ₁ : Matrix n n' k → ℂ) (h₁ : Ψ₁ ∈ SB (Matrix n n' k)) (Ψ₂ : Matrix n'' n k → ℂ)
      (h₂ : Ψ₂ ∈ SB (Matrix n'' n k)) (a a' b b' : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (ha' : a' ∈ SB (n → k))
      (hb : b ∈ SB (n → k)) (hb' : b' ∈ SB (n → k)),
      fpair χ e μ a' b' • (Θ v (col Ψ₁ h₁ a ha) (row Ψ₂ h₂ b hb)).1 =
        fpair χ e μ a b • (Θ v (col Ψ₁ h₁ a' ha') (row Ψ₂ h₂ b' hb')).1 := by
    intro v Ψ₁ h₁ Ψ₂ h₂ a a' b b' ha ha' hb hb'
    rw [hΘ, hΘ]
    exact HC n n' n'' σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ L₁ L₂ L₂' L₃ f₁ _ _ f₂ _ _ Ψ₁ Ψ₂ a a' b b' ha ha' hb hb'
      (a₁ (col Ψ₁ h₁ a ha)) (a₁ (col Ψ₁ h₁ a' ha')) (a₂ (row Ψ₂ h₂ b hb)) (a₂ (row Ψ₂ h₂ b' hb')) v.1 v.2
  have hFF : ∀ A : Pair k n', IsContAut B.A (FFStar q (resChar χ hχ q) φ A) := fun A => by
    have := (FFStar q (resChar χ hχ q) (fun P₂ => (⟨φ P₂, hφ.2.2 P₂⟩ : caSub B.A)) A).2
    rwa [val_FFStar'] at this
  let v' : caSub B.A := ⟨_, hFF P⟩
  let x : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
    col (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (charInd (resChar χ hχ q) Q') (charInd_mem' _ Q')
  let xv : Pair k n' → Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun A Q' =>
    col (phiOne A Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem A Q') (vecInd Q.lat) hvec
  let yd : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
    row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (dualInd Q.lat) hdual
  let y₀ : SB (Matrix (n'' ⊕ Fin 1) n k) := row (latInd Q.lat R.ker) (latInd_mem_SB _ _) (dualInd Q.lat) hdual
  let y : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
    row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (cosetInd q Q''.lat Q''.red) (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _)

  have h2 : hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = ((r₁ : ℂ) * chrPow s₁.χW (p.idele q.unit) e₁) •
      hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P) (U₁ (∑ Q' ∈ withLat Q.lat, x Q')) Ξ₂ :=
    lift_step s₁ s₂ l vL (hFF P) U₁ t₁ (withLat Q.lat) x Ξ₁ Ξ₂
      (HS ψ B.V₀ B.A B.L J.W₀ B.o B.ζ B.line B.cpt B.vA s₁.χV s₁.χW s₁.om₀ s₁.weil₀ hu₁.1 hu₁.2 α α₀ β hα P Q.lat
        L₁ L₂ f₁ Ξ₁ (fun Q' => U₁ (x Q')) o₁ (fun Q' _ => a₁ (x Q')) φ hφ)

  have hΞ₂ : Ξ₂ = U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'') := by
    rw [b₂ ⟨_, o₂.2.2.2.1⟩ Ξ₂ o₂]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum]
    exact D2 R

  have t0 : ∀ Q' ∈ withLat Q.lat, (Θ v' (x Q') y₀).1 = 0 := fun Q' hQ' => by
    have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (latInd Q.lat R.ker) (latInd_mem_SB _ _)
      (charInd (resChar χ hχ q) Q') (vecInd Q.lat) (dualInd Q.lat) (dualInd Q.lat) (charInd_mem' _ Q') hvec hdual hdual
    have hf := GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q'
    rw [mem_withLat.1 hQ'] at hf
    rw [hf, zero_smul] at this
    exact (smul_eq_zero.1 this).resolve_left I0

  have t1 : ∀ Q' ∈ withLat Q.lat, ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1 =
      (Θ v' (xv P Q') (yd (ε • Q'))).1 := by
    intro Q' hQ'
    have hQ'l : Q'.lat = Q.lat := mem_withLat.1 hQ'
    have hmem : ε • Q' ∈ withLat Q.lat := mem_withLat.2 (by rw [Pair.dia_lat, hQ'l])
    rw [Finset.sum_eq_single_of_mem (ε • Q') hmem]
    · have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (phiOne (ε • Q') R)
        (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
        (cosetInd q (ε • Q').lat (ε • Q').red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
      rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' (ε • Q') (by rw [Pair.dia_lat])).1 rfl, hQ'l] at this
      exact smul_right_injective _ I0 this
    · intro Q'' hQ'' hne
      have hQ''l : Q''.lat = Q.lat := mem_withLat.1 hQ''
      have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (phiOne Q'' R)
        (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
        (cosetInd q Q''.lat Q''.red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
      rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' Q'' (hQ''l.trans hQ'l.symm)).2 hne, zero_smul] at this
      exact (smul_eq_zero.1 this).resolve_left I0

  have hmove : ∀ (Q₀ : Pair k n) (g : GL n k), g • Q.lat = Q.lat →
      (Θ v' (xv P (g • Q₀)) (yd (g • ε • Q₀))).1 = (Θ v' (xv P Q₀) (yd (ε • Q₀))).1 := by
    intro Q₀ g hgL
    have hdet := GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.valuation_det_of_fix Q.lat hgL
    have hgL' : g⁻¹ • Q.lat = Q.lat := by
      conv_lhs => rw [← hgL]
      exact inv_smul_smul g Q.lat
    have e1 : s₁.om₀ (α₀.gl 1, β.gl g) (U₁ (xv P Q₀)) = U₁ (xv P (g • Q₀)) := by
      refine b₁ _ _ ?_
      have := (lin₁ _ _ α₀ β L₁ L₂ f₁ _ _ (a₁ (xv P Q₀))).1 1 g
      convert this using 1
      funext z
      have hl : ((lS₁ (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin 1) k)) : ℂˣ) : ℂ) = 1 := by simp
      have hr : ((lT₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := by rw [vT₁ _ hdet]; rfl
      show tensCol (phiOne P (g • Q₀)) (vecInd Q.lat) z = _ * _ * tensCol (phiOne P Q₀) (vecInd Q.lat) _
      rw [hl, hr, one_mul, one_mul,
        show (1 : GL (n' ⊕ Fin 1) k) = GlobalTheory.RootEx.embX 1 (1 : GL n' k) from (map_one _).symm,
        tensCol_subst' (vecInd Q.lat) ((g⁻¹ : GL n k) : Matrix n n k) (1 : GL n' k)
          (Ψ' := phiOne P (g • Q₀)) (fun x => by
            have := phiOne_smul (P := P) (Q := Q₀) (x := x) (1 : GL n' k) g
            rw [one_smul] at this
            exact this) z]
      congr 1
      funext w
      exact (vecInd_mulVec hgL' w).symm
    have e2 : s₂.om₀ (β.gl g, γ₀.gl 1) (U₂ (yd (ε • Q₀))) = U₂ (yd (g • ε • Q₀)) := by
      refine b₂ _ _ ?_
      have := (lin₂ _ _ β γ₀ L₂' L₃ f₂ _ _ (a₂ (yd (ε • Q₀)))).1 g 1
      convert this using 1
      funext z
      have hl : ((lS₂ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := by rw [vS₂ _ hdet]; rfl
      have hr : ((lT₂ (Matrix.GeneralLinearGroup.det (1 : GL (n'' ⊕ Fin 1) k)) : ℂˣ) : ℂ) = 1 := by simp
      show tensRow (phiOne (g • ε • Q₀) R) (dualInd Q.lat) z = _ * _ * tensRow (phiOne (ε • Q₀) R) (dualInd Q.lat) _
      rw [hl, hr, one_mul, one_mul,
        show (1 : GL (n'' ⊕ Fin 1) k) = GlobalTheory.RootEx.embX 1 (1 : GL n'' k) from (map_one _).symm,
        tensRow_subst' (dualInd Q.lat) (1 : GL n'' k) (g : Matrix n n k)
          (Ψ' := phiOne (g • ε • Q₀) R) (fun x => by
            have := phiOne_smul (P := ε • Q₀) (Q := R) (x := x) g (1 : GL n'' k)
            rw [one_smul] at this
            exact this) z]
      congr 1
      funext w
      exact (dualInd_vecMul hgL w).symm
    have e3 := Comm.doubleThetaUnfolding_equivariant_unitaryGroups s₁ s₂ l vL (hFF P) (t₁ (xv P Q₀)) (t₂ (yd (ε • Q₀))) 1 (β.gl g) 1
    rw [one_emb, one_emb] at e3
    rw [hΘ, hΘ, ← e1, ← e2, map_one α₀.gl, map_one γ₀.gl]
    rw [show (fun x : GA D B.A => FFStar q (resChar χ hχ q) φ P (x * 1)) = FFStar q (resChar χ hχ q) φ P from
      funext fun x => by rw [mul_one]] at e3
    rw [e3]
    funext x
    rw [mul_one]
  have hall : ∀ Q' ∈ withLat Q.lat, (Θ v' (xv P Q') (yd (ε • Q'))).1 =
      (Θ v' (xv P (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 := by
    intro Q' hQ'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (ε⁻¹ • Q) Q'
    have hgL : g • Q.lat = Q.lat := by
      have := congrArg Pair.lat hg
      rw [Pair.smul_lat, Pair.dia_lat, mem_withLat.1 hQ'] at this
      exact this
    have := hmove (ε⁻¹ • Q) g hgL
    rw [hg, smul_comm g ε (ε⁻¹ • Q), hg] at this
    exact this

  have hid : ∀ Y', s₂.om₀ (1, 1) Y' = Y' := fun Y' => by
    rw [show ((1 : GA D J.W₀), (1 : GA D B'.V₀)) = 1 from rfl, map_one]
    rfl
  have hsrc : ∀ (g : GL n' k), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 → ∀ A A' : Pair k n',
      hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ (g • A)) (U₁ (xv (g • A') Q)) (U₂ (yd Q)) =
        hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ A) (U₁ (xv A' Q)) (U₂ (yd Q)) := by
    intro g hdet A A'
    have e1 : s₁.om₀ (α₀.gl (GlobalTheory.RootEx.embX 1 g), β.gl 1) (U₁ (xv A' Q)) = U₁ (xv (g • A') Q) := by
      refine b₁ _ _ ?_
      have := (lin₁ _ _ α₀ β L₁ L₂ f₁ _ _ (a₁ (xv A' Q))).1 (GlobalTheory.RootEx.embX 1 g) 1
      convert this using 1
      funext z
      have hl : ((lS₁ (Matrix.GeneralLinearGroup.det (GlobalTheory.RootEx.embX 1 g)) : ℂˣ) : ℂ) = 1 := by
        rw [det_embX_one', vS₁ _ hdet]; rfl
      have hr : ((lT₁ (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂˣ) : ℂ) = 1 := by simp
      show tensCol (phiOne (g • A') Q) (vecInd Q.lat) z = _ * _ * tensCol (phiOne A' Q) (vecInd Q.lat) _
      rw [hl, hr, one_mul, one_mul,
        tensCol_subst' (vecInd Q.lat) (((1 : GL n k)⁻¹ : GL n k) : Matrix n n k) g
          (Ψ' := phiOne (g • A') Q) (fun x => by
            have := phiOne_smul (P := A') (Q := Q) (x := x) g (1 : GL n k)
            rw [one_smul] at this
            exact this) z]
      congr 1
      funext w
      simp
    have e3 := Comm.doubleThetaUnfolding_equivariant_unitaryGroups s₁ s₂ l vL (hFF A) (t₁ (xv A' Q)) (t₂ (yd Q)) (α.gl g) 1 1
    rw [one_emb, Comm.emb_gl hα g, hid] at e3
    have e4 : FFStar q (resChar χ hχ q) φ (g • A) = fun x => FFStar q (resChar χ hχ q) φ A (x * α.gl g) :=
      FFStar_mem_EqForm q _ hφ.1 g A
    rw [e4, ← e1, map_one β.gl, e3]
    funext x
    rw [mul_one]
  obtain ⟨g₁, hg₁a, hg₁b, hg₁d⟩ : ∃ g₁ : GL n' k, g₁ • P = ε • P ∧ g₁ • (ε • P) = P ∧
      valuation k ((Matrix.GeneralLinearGroup.det g₁ : kˣ) : k) = 1 := by
    rcases hεe with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨1, by rw [h, one_smul, one_smul], by rw [h, one_smul, one_smul], by simp⟩
    · refine ⟨-1, by rw [neg_one_smul_pair, h], ?_, val_det_neg_one⟩
      rw [neg_one_smul_pair, h, smul_smul]
      simp
  have hfin : (Θ v' (xv P (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 =
      hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P) Ξ₁' Ξ₂' := by
    rw [hΘ, b₁ (xv P Q) Ξ₁' o₁', b₂ (yd Q) Ξ₂' o₂', dia_apply, smul_inv_smul]
    have hx : xv P (ε⁻¹ • Q) = xv (ε • P) Q := by
      apply Subtype.ext
      show tensCol (phiOne P (ε⁻¹ • Q)) _ = tensCol (phiOne (ε • P) Q) _
      have := phiOne_dia (P := P) (Q := ε⁻¹ • Q) ε
      rw [smul_inv_smul] at this
      rw [this]
    rw [hx]
    have := hsrc g₁ hg₁d P (ε • P)
    rw [hg₁a, hg₁b] at this
    exact this.symm
  have hexp : hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P) (U₁ (∑ Q' ∈ withLat Q.lat, x Q'))
      (U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'')) =
      ∑ Q' ∈ withLat Q.lat, ((Θ v' (x Q') y₀).1 + ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1) := by
    refine (hΘ v' _ _).symm.trans ?_
    rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun Q' _ => ?_
    rw [map_add, map_sum, Submodule.coe_add, Submodule.coe_sum]
  rw [h2, hΞ₂, hexp, Finset.sum_congr rfl fun Q' hQ' => by rw [t0 Q' hQ', zero_add, t1 Q' hQ', hall Q' hQ'],
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hfin, card_withLat_eq_pairCount Q]
  congr 1
  push_cast
  ring

end GlobalTheory.FinPl.VertexExactCount
end
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant : ∀ D : D7, GlobalTheory.FinPl.VertexExact D := by
  atlas_forward_decl GlobalTheory.FinPl.VertexExactCount.vertexExact
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VertexAllProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem over_self {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] {α : Frame p S m'} {β : Frame p T m}
    {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ} (h : Over ψ α β LS LT g Φ f) (hU : p.UnitAA)
    (ΛS : Submodule 𝒪[k] (m' → k)) (ΛT : Submodule 𝒪[k] (m → k)) (hLS : α.IsLat LS ΛS) (hLT : β.IsLat LT ΛT) :
    Over ψ α β LS LT g (latInd ΛS ΛT) g := by
  obtain ⟨hS, hT, hvac, -, ⟨Tm, hTm⟩, -⟩ := h
  have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p m m' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
  refine ⟨hS, hT, hvac, GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat D k p m m' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
  have hv := hT'.vac
  rw [one_smul] at hv
  change g = T' (extFun α β (latInd ΛS ΛT))
  rw [hE, hv]

theorem overAll_nil {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

end GlobalTheory.FinPl.VertexAllProof

open GlobalTheory.FinPl.VertexAllProof in

theorem GlobalTheory.FinPl.vertexAll : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  intro D k _ _ _ _ ι p I P hPl q ψ χ hχ hc
  have hvg := fun i => GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant D k (p i) q ψ (χ i) (hχ i) (hc i)
  refine ⟨fun i => (hvg i).choose, fun i => (hvg i).choose_spec.1, ?_⟩
  intro n n' n'' _ _ _ _ _ _
  have hrc := fun i => (hvg i).choose_spec.2 n n' n''
  choose r e hr hre using hrc
  refine ⟨r, e, hr, ?_⟩
  intro σ B J B' s₁ s₂ l vL hunr a b a' M₀ M₁ M₂ _ _ _ hgl Ξ₁ Ξ₂ _ _
  have hP : ∀ i, P (p i).v := fun i => (hPl.mem _).2 ⟨i, rfl⟩
  have hmaps : ∀ (ls : List ι) (φ : GA D B.A → ℂ), a.Ram φ →
      a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) := fun ls φ hφ =>
    (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι p q χ hχ (fun i => (hvg i).choose) n' B.A B.V₀ a hPl.inj ls).1.mapsTo hφ
  have hV : ∀ ls : List ι, ∀ Ξ₁' Ξ₂',
      OverAll ψ a.α₀ b.β M₀ M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) ls Ξ₁ Ξ₁' →
      OverAll ψ b.β a'.α₀ M₁ M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) ls Ξ₂ Ξ₂' →
      ∀ φ, a.Ram φ → hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
        (ls.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
          hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) Ξ₁' Ξ₂' := by
    intro ls
    induction ls with
    | nil =>
      intro Ξ₁' Ξ₂' h1 h2 φ _
      rw [overAll_nil.1 h1, overAll_nil.1 h2, List.map_nil, List.prod_nil, one_smul]
      rfl
    | cons i ls ih =>
      intro Ξ₁' Ξ₂' h1 h2 φ hφ
      obtain ⟨g₁, hg₁, hΞ₁'⟩ := overAll_cons.1 h1
      obtain ⟨g₂, hg₂, hΞ₂'⟩ := overAll_cons.1 h2
      have ho₁ := over_self hΞ₁' (hgl i).1.unit _ _ (hgl i).1.lat (hgl i).2.2
      have ho₂ := over_self hΞ₂' (hgl i).1.unit _ _ (hgl i).2.2 (hgl i).2.1.lat
      obtain ⟨F, hF, hFP⟩ := (hmaps ls φ hφ).2 i
      have hv := hre i (a.P i) (b.Q i) (a'.P i) σ B J B' s₁ s₂ l vL (hunr _ (hP i)).1 (hunr _ (hP i)).2 (a.α i)
        (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (hgl i).1.sum (hgl i).2.1.sum M₀ M₁ M₁ M₂ g₁ g₁ Ξ₁' g₂ g₂ Ξ₂' ho₁ hΞ₁'
        ho₂ hΞ₂' F hF
      have hsop := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n' q (χ i) (hχ i) _ rfl ((hvg i).choose) B.A (a.α i) (a.P i)).2.1 F hF).2
      rw [ih g₁ g₂ hg₁ hg₂ φ hφ, ← hFP, hv, ← hsop, hFP, smul_smul, List.map_cons, List.prod_cons, mul_comm]
      rfl
  intro Ξ₁' Ξ₂' h1 h2 φ hφ
  exact hV I Ξ₁' Ξ₂' h1 h2 φ hφ
end
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  atlas_forward_decl GlobalTheory.FinPl.vertexAll
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem mxAt_mul_right (P : Pl D → Prop) {m n r : ℕ} {x : Mx D m n} (hx : MxAt P x) (M : Matrix (Fin n) (Fin r) (AE D)) :
    MxAt P (x * M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left (P : Pl D → Prop) {m n r : ℕ} {x : Mx D n r} (hx : MxAt P x) (M : Matrix (Fin m) (Fin n) (AE D)) :
    MxAt P (M * x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem combAt_extS (P : Pl D → Prop) {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extS o T c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (w ⬝ o.pA + (0 : WO L T) ⬝ o.pB) i j ∈ idAt D P
  rw [Matrix.zero_mul, add_zero]
  exact mxAt_mul_right P (hc w hw) _ i j

theorem combAt_extT (P : Pl D → Prop) {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extT o S c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (o.jA ⬝ w + o.jB ⬝ (0 : WO S L)) i j ∈ idAt D P
  rw [Matrix.mul_zero, add_zero]
  exact mxAt_mul_left P (hc w hw) _ i j

theorem isFinComb_of_combAt (P : Pl D → Prop) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  exact (RingHom.mem_ker).1 (Ideal.mem_inf.1 (hc u hu i j)).1

theorem places_of_preT {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} {o : TDat c k ι} (H : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨H.nodup, H.all, H.inj, fun x => H.tP x, fun i => (H.char i).2⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [heisO]

theorem vac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) :
    Vac ψ S T LS LT P (fun _ => 0) :=
  ⟨GlobalTheory.OrientedHeis.theta_zero, fun u _ => heisO_zero ψ S T _, fun _ _ u _ _ => heisO_zero ψ S T u⟩

theorem biVacAt_zero (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A')
    (P : Pl D → Prop) : BiVacAt ψ LA LS LA' P (fun _ _ => 0) :=
  ⟨fun _ => vac_zero ψ A S LA LS P, fun _ => vac_zero ψ S A' LS LA' P⟩

theorem comb_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : comb ψ S T c (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [comb, heisO_zero]

theorem biComb_zero (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    biComb ψ A S A' c c' (fun _ _ => 0) = fun _ _ => 0 := by
  funext u v
  simp only [biComb, comb_zero]

theorem biLift_zero {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) :
    biLift oma omb vA vS φ (fun _ _ => 0) = 0 := by
  funext h₂
  simp only [biLift]
  have e1 : ∀ h₀ h₁, (fun v : WO S A' => oma (h₀, h₁) (fun _ => 0) 0) = 0 := fun h₀ h₁ => by
    funext v; exact congrFun (map_zero (oma (h₀, h₁))) 0
  simp only [e1, map_zero, Pi.zero_apply, mul_zero, MeasureTheory.integral_zero]

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem bl_contr (hCL : ContrLaw D) {c : Comm D} (v : VCom c) (t : Tup c) (hW : WeilOK (t := t) v) {j σ : ℕ}
    (h : j + 2 * (σ + 1) + 2 = D.R.m) {φ : GA D (c.X j) → ℂ} (hφ : IsContAut (c.X j) φ)
    {Ξ₁ : WO (c.B j (σ + 1) h).V₀ (c.X (j + 1)) → ℂ} {Ξ₂ : WO (c.X (j + 1)) (c.B (j + 1 + 1) σ (idx_step h)).V₀ → ℂ}
    (h₁ : IsThetaFunO c.ψ _ _ Ξ₁) (h₂ : IsThetaFunO c.ψ _ _ Ξ₂) :
    c.bl j (t.kom j) (t.kom (j + 1)) φ (GlobalTheory.Unf.contr (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) Ξ₁ Ξ₂) =
      hand0 (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) φ Ξ₁ Ξ₂ := by
  obtain ⟨χA, χA', χz, omz, omz', e1, e2, w1, w2, w3, w4⟩ := hW.mid j σ h
  funext g
  have := (hCL c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz (t.kom j) omz
    (t.kom (j + 1)) omz' e1 e2 w1 w2 w3 w4 φ Ξ₁ Ξ₂ hφ h₁ h₂).2.2 g
  rw [hand0, this]
  rfl

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem lastKer_isLattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : (lastKer L).IsLattice k := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq q]
  exact gluedLat_isLattice q 1 2 L 0

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

theorem lawLevelPrime_double : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  intro D c v k _ _ _ _ ι o hc hv hS j σ h
  have hPl := places_of_preT hS.pre
  obtain ⟨x₀⟩ := Formalism.L2.Col.nonempty_places D.host.F
  have hstd := hc.std
  have sd0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have sd1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have sd2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have sdG : IsSelfDualC _ (o.M j (σ + 1) h) := ((hS.good x₀).bf j (σ + 1) h).sdV₀
  have sdG' : IsSelfDualC _ (o.M (j + 1 + 1) σ (idx_step h)) := ((hS.good x₀).fb j σ h).sdW₀
  obtain ⟨M0, sdM0, latM0, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ j (σ + 1) h) (o.M j (σ + 1) h) sdG
    (fun i => lastKer (o.Q j i).lat) (fun i => lastKer_isLattice o.q _)
  obtain ⟨M0', sdM0', latM0', -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ (j + 1 + 1) σ (idx_step h))
    (o.M (j + 1 + 1) σ (idx_step h)) sdG' (fun i => lastKer (o.Q (j + 1 + 1) i).lat) (fun i => lastKer_isLattice o.q _)
  obtain ⟨e1, e1', he1, he1', hR1⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1)
    c.ψ hstd _ _ (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) M0 (c.x (j + 1)).L (c.x (j + 1)).L sdG sd1 sdM0 sd1
  obtain ⟨e2, e2', he2, he2', hR2⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1)
    (Fin (c.X (j + 1)).rank) c.ψ hstd _ _ (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (c.x (j + 1)).L
    (o.M (j + 1 + 1) σ (idx_step h)) M0' sd1 sdG' sd1 sdM0'

  have hext1 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.bes j (σ + 1) h).V₀ (c.X j) (c.bes j (σ + 1) h).L (c.X (j + 1)) (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ
    (c.bes j (σ + 1) h).line (o.β j) (o.β₀ j (σ + 1) h) (o.β (j + 1)) (fun i => (hS.glued j (σ + 1) h i).sum)
    (c.x j).L M0 (c.x (j + 1)).L (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1) i).lat) sd0 sdM0 sd1
    (fun i => ⟨hS.pre.latT j (by omega) i, latM0 i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hext2 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (c.bes (j + 1 + 1) σ (idx_step h)).V₀ (c.X (j + 1 + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).L (c.X (j + 1))
    (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ (c.bes (j + 1 + 1) σ (idx_step h)).line
    (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (o.β (j + 1)) (fun i => (hS.glued (j + 1 + 1) σ (idx_step h) i).sum)
    (c.x (j + 1 + 1)).L M0' (c.x (j + 1)).L (fun i => (o.Q (j + 1 + 1) i).lat) (fun i => (o.Q (j + 1) i).lat) sd2 sdM0' sd1
    (fun i => ⟨hS.pre.latT (j + 1 + 1) (by omega) i, latM0' i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hrep1 : Reps c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I
      (· ∈ v.tP) (v.dT j) := ⟨(hv.atT j).1, hS.rep j (by omega)⟩
  have hrep2 : Reps c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (o.Q (j + 1) i) (o.Q (j + 1 + 1) i)) o.I (· ∈ v.tP) (v.dT (j + 1)) :=
    ⟨(hv.atT (j + 1)).1, hS.rep (j + 1) (by omega)⟩
  have hX1 := hext1.2.1 _ _ hrep1
  have hX2 := hext2.2.2 _ _ hrep2
  obtain ⟨op0, hop0, hC⟩ := GlobalTheory.T.contractionOfVacuumCombinations_proof D k ι o.p o.I _ hPl (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (o.β j)
    (o.β₀ j (σ + 1) h) (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) M0 (c.x (j + 1)).L M0'
    (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1 + 1) i).lat) sdM0 sd1 sdM0'
    (fun i => ⟨(hS.glued j (σ + 1) h i).sum, (hS.glued (j + 1 + 1) σ (idx_step h) i).sum, latM0 i, latM0' i⟩) e1' e2' he1' he2'
  have hInv := (GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).1 (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L
    sd0 sd1 sd2
  obtain ⟨ε, -, hV⟩ := GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof D k ι o.p o.I _ hPl o.q c.ψ o.χ o.hχ (fun i => (hS.pre.char i).1)
  obtain ⟨r, e, hr, hVE⟩ := hV (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank)

  let a : PairDat o.p (c.B j (σ + 1) h).A (c.B j (σ + 1) h).V₀ (Fin (c.X j).rank) := ⟨o.β j, o.β₀ j (σ + 1) h, o.Q j⟩
  let b : MidDat o.p (c.J j (σ + 1) h).W₀ (Fin (c.X (j + 1)).rank) := ⟨o.β (j + 1), o.Q (j + 1)⟩
  let a' : PairDat o.p (c.B (j + 1 + 1) σ (idx_step h)).A (c.B (j + 1 + 1) σ (idx_step h)).V₀ (Fin (c.X (j + 1 + 1)).rank) :=
    ⟨o.β (j + 1 + 1), o.β₀ (j + 1 + 1) σ (idx_step h), o.Q (j + 1 + 1)⟩
  have hcore : ∀ i, GluedCore (c.B j (σ + 1) h) (o.M j (σ + 1) h) o.q (a.α i) (a.α₀ i) (a.P i) ∧
      GluedCore (c.B (j + 1 + 1) σ (idx_step h)) (o.M (j + 1 + 1) σ (idx_step h)) o.q (a'.α i) (a'.α₀ i) (a'.P i) ∧
      (b.β i).IsLat (c.x (j + 1)).L (b.Q i).lat := fun i =>
    ⟨hS.glued j (σ + 1) h i, hS.glued (j + 1 + 1) σ (idx_step h) i, hS.pre.latT (j + 1) (by omega) i⟩
  have hOrth : ∀ x, x ∈ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o M0 (c.x j).L LL x) ∧
      ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o M0' (c.x (j + 1 + 1)).L LL x := fun x hx => ⟨hext1.1 x hx, hext2.1 x hx⟩

  have key : ∀ t : Tup c, ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ →
      Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
      ∃ f₁ f₂, Vac c.ψ _ _ (o.M j (σ + 1) h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j (σ + 1) h) Ψ₁) ∧
        Vac c.ψ _ _ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) (· ∈ v.tP) (flatFB (t.sFB j σ h) Ψ₂) ∧
        Vac c.ψ _ _ M0 (c.x (j + 1)).L (· ∈ v.tP) f₁ ∧ Vac c.ψ _ _ (c.x (j + 1)).L M0' (· ∈ v.tP) f₂ ∧
        c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = op0.app c.ψ (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        OverAll c.ψ a.α₀ b.β (o.M j (σ + 1) h) (c.x (j + 1)).L
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) o.I
          (flatBF (t.sBF j (σ + 1) h) Ψ₁) (comb c.ψ _ _ (extS (c.bes j (σ + 1) h).o (c.X (j + 1)) (v.dT j)) f₁) ∧
        OverAll c.ψ b.β a'.α₀ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h))
          (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) o.I
          (flatFB (t.sFB j σ h) Ψ₂) (comb c.ψ _ _ (extT (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (v.dT (j + 1))) f₂) := by
    intro t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hF := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
    have hXi1 := hF.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h) (v.N (j + 1))
      (c.x (j + 1)).L (fun x _ => (hS.good x).bf j (σ + 1) h) Ψ₁ hΨ₁
    have hXi2 := hF.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hS.good x).fb j σ h) Ψ₂ hΨ₂
    obtain ⟨hf1, hinv1, hov1⟩ := hR1 _ hXi1
    obtain ⟨hf2, hinv2, hov2⟩ := hR2 _ hXi2
    refine ⟨_, _, hXi1, hXi2, hf1, hf2, ?_, ?_, ?_, ?_⟩
    · have := hC _ _ hf1 hf2
      rw [hinv1, hinv2] at this
      exact this
    · exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) _ _ hf1.1 hf2.1).2.2 (· ∈ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L M0 M0' sd0 sd1 sd2 sdM0 sdM0'
        hOrth hf1 hf2
    · exact (hov1 _ _).2 (hX1.2 _ hf1)
    · exact (hov2 _ _).2 (hX2.2 _ hf2)

  have hCL : ContrLaw D := GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D
  have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
    (c.vL j σ h)
  rcases hInv with hz | ⟨op', hop', hinv⟩
  ·
    have happ : ∀ C, BiOp.app c.ψ (⟨0, Fin.elim0, Fin.elim0⟩ : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) C = fun _ _ => 0 :=
      fun C => by funext u w; simp [BiOp.app]
    refine ⟨ε, ⟨0, Fin.elim0, Fin.elim0⟩, r, e, hr, fun i => i.elim0, ?_⟩
    intro t _ _ _ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, -, -, -, -, hctr, hC0, -, -⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have h0 : c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = fun _ _ => 0 := by rw [hctr, hz _ hC0]; rfl
    refine ⟨by rw [happ]; exact biVacAt_zero _ _ _ _ _, fun d d' _ _ φ _ => ?_⟩
    rw [h0, happ, biComb_zero, biComb_zero, biComb_zero]
    simp only [Comm.bl, biLift_zero, smul_zero]
  · refine ⟨ε, op', r, e, hr, hop', ?_⟩
    intro t _ hW hU Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, hXi1, hXi2, hf₁, hf₂, hctr, hC0, hov1, hov2⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hback : op'.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) = (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) := by
      rw [hctr]; exact hinv _ hC0
    refine ⟨by rw [hback]; exact hC0, fun d d' hd hd' φ hφ => ?_⟩
    rw [hback]
    have hD1 := combAt_extS (fun x => x ∉ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) hd
    have hD2 := combAt_extT (fun x => x ∉ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) hd'
    have hT1 := combAt_extS (· ∈ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) (hv.atT j).1
    have hT2 := combAt_extT (· ∈ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (hv.atT (j + 1)).1
    have hAC1 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd _ _
      (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) (c.x (j + 1)).L sdG sd1
      (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat))).2.2 _ hD1 _ hXi1
    have hAC2 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1) (Fin (c.X (j + 1)).rank) c.ψ hstd _ _
      (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sd1 sdG'
      (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat))).2.2 _ hD2 _ hXi2
    have th1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT1) hf₁.1
    have th2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT2) hf₂.1
    have thD1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD1) th1'
    have thD2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD2) th2'
    have hVx := hVE σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h) (t.sFB j σ h)
      (c.lnk j σ h) (c.vL j σ h) (fun x hx => ⟨hU.bf j (σ + 1) h x hx, hU.fb j σ h x hx⟩) a b a' (o.M j (σ + 1) h)
      (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sdG sd1 sdG' hcore _ _ hAC1.1 hAC2.1 _ _ (hAC1.2 _ hov1)
      (hAC2.2 _ hov2) φ hφ
    have hSφ : IsContAut (c.X j) (a.sAll o.q (fun i => resChar (o.χ i) (o.hχ i) o.q) ε o.I φ) :=
      ((GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) _ _ a hS.pre.inj o.I).1.mapsTo hφ).1
    have e1 := (hCC _ _ hXi1.1 hXi2.1).2.1 d d'
    have e2 := bl_contr hCL v t hW h hφ.1 hAC1.1.1 hAC2.1.1
    have e4 := bl_contr hCL v t hW h hSφ thD1' thD2'
    have e5 := (hCC _ _ th1' th2').2.1 d d'
    have e6 := (hCC _ _ hf₁.1 hf₂.1).2.1 (v.dT j) (v.dT (j + 1))
    show c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂))) = _
    rw [← e1, e2, hVx, ← e4, e5, e6]
    rfl

end GlobalTheory.LevPrimeMid
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  atlas_forward_decl GlobalTheory.LevPrimeMid.lawLevelPrime_double
end

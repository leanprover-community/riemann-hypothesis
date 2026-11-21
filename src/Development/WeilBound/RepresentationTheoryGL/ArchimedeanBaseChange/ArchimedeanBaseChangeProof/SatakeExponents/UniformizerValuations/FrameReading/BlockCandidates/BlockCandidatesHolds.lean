import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandidatesOfInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ProjAlg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PLimAtOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandSb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandTb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandLh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IsOpenChiMu
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PairDoubleCosetFiniteSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.RExpReadOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Imports
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealReadLevi

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem restr {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (S T : StarSubalgebra ℂ A) (hle : S ≤ T)
    (χ : T →⋆ₐ[ℂ] ℂ) : ∃ χ' : S →⋆ₐ[ℂ] ℂ, ∀ (y : A) (hy : y ∈ S) (hy' : y ∈ T), χ' ⟨y, hy⟩ = χ ⟨y, hy'⟩ :=
  ⟨χ.comp (StarSubalgebra.inclusion hle), fun _ _ _ => rfl⟩

section Gen

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem gen_tr (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ)
    (c : Γ → ℂ) (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (h : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) →
      (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q) : GRead gen β m v Q := by
  intro s χ h1 h2 h3
  have hle : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) ≤
      StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪
        {star (β s ^ m) * β s ^ m}) := by
    refine StarAlgebra.adjoin_le ?_
    rintro y (⟨x, rfl⟩ | hy)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  obtain ⟨χ', e⟩ := restr _ _ hle χ
  refine h s χ' (fun y => ?_) (fun x => ?_) ?_
  · exact (congrArg norm (e y.1 y.2 (hle y.2))).trans_le (h1 ⟨y.1, hle y.2⟩)
  · have p := ChiPin.chi_pin gen a₀ v hv (by rw [hc, h₀, one_smul]) s _ χ h2
      ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x)
    exact (e _ _ _).trans p
  · exact (e _ _ _).trans_ne h3

end Gen

set_option maxHeartbeats 2000000 in
theorem chiTr' : ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h₀ h =>
  gen_tr (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h₀ Q
    fun s χ h1 h2 h3 => h s χ ⟨h1, h2, h3⟩

end PositivityTheory.Rg.BcB.F.BC

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
  {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)}
  {μb : Measure (G b)}

theorem prod_valW_ite (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) {k : ℕ} (χ : InfinitePlace E → Inf k) (v : InfinitePlace E)
    (w : List (Bool × ℕ)) (p : Prop) [Decidable p] :
    (∏ v', A.valW (if v' = v ∧ p then w else []) (χ v')) =
      (if p then zVal w (χ v) else 1) * ∏ v', A.valW [] (χ v') := by
  have e : ∀ v', A.valW (if v' = v ∧ p then w else []) (χ v') =
      (if v' = v then (if p then zVal w (χ v) else 1) else 1) * A.valW [] (χ v') := by
    intro v'
    by_cases h1 : v' = v
    · subst h1
      by_cases hp : p
      · simp [hp, Arch.valW, zVal]
      · simp [hp]
    · simp [h1]
  rw [Finset.prod_congr rfl fun v' _ => e v', Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)

theorem val_tD (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool)
    (χa : InfinitePlace E → Inf (F.B i).a) (χb : InfinitePlace E → Inf (F.B i).b) :
    (F.tD i v s m side).val χa χb =
      (if side then zVal [(s, m)] (χb v) else zVal [(s, m)] (χa v)) * (F.t₀ i).val χa χb := by
  simp only [PT.val, valA, RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
  rw [prod_valW_ite, prod_valW_ite]
  cases side <;> simp <;> ring

end

set_option maxHeartbeats 2000000 in
theorem identOf' : IdentOf := by
  intro hG hR E _ _ _ n π S T F₀ F i χ hχ O
  have h0 := O.eigArch (.inl ()) (F.t₀ i) rfl rfl
  have h3 := hχ.2.1 (.inl ())
  have one : (F.t₀ i).val O.χa O.χb = 1 := by
    rw [← h0]
    exact h3
  have key : ∀ (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool),
      (if side then zVal [(s, m)] (O.χb v) else zVal [(s, m)] (O.χa v)) =
        (if side then zVal [(s, m)] ((F₀.A i).χb v) else zVal [(s, m)] ((F₀.A i).χa v)) := by
    intro v s m side
    have h1 := O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (by simp [RunFrame.g]) rfl
    have h2 := hχ.2.1 (.inr (.inl (i, v, s, m, side)))
    rw [val_tD, one, mul_one] at h1
    rw [← h1, h2]
    cases side <;> rfl
  constructor
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m false
    simpa [zVal] using this
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m true
    simpa [zVal] using this

end PositivityTheory.Rg.BcB.F.BC

end
end

section
namespace PositivityTheory.Rg.BcB.F.BC

theorem block_candidates_holds : BlockCand := block_candidates_of_inputs chiTr' limAt_holds (identOf' gamma_zeta_nabla_cancel.gelfInj)

end PositivityTheory.Rg.BcB.F.BC
end

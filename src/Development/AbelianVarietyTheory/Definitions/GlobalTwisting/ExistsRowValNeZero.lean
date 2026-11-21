import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.KerRat

namespace GlobalTheory.PerQ.Model

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)


theorem span_toMtP_gen (hX : X.Ok) (σ : X.K →+* ℂ) :
    Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) = ⊤ := by
  refine toCForm_span_of_span σ W.sgTrue _ _ hX (φ := fun z : MtildeL W Ch sel mu P => z.1) ?_
  exact (congrArg (Submodule.span X.K) Subtype.range_coe).trans (MtildeH_good W Ch hX sel mu P).2.2

end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

theorem rowVal_add {u : B.Word} {a : I.ι} {G G' : (I.per l u a).Mt} (h : RowVal I l u a G) (h' : RowVal I l u a G') :
    RowVal I l u a (G + G') := fun c => by
  obtain ⟨y, hy, e⟩ := h c
  obtain ⟨y', hy', e'⟩ := h' c
  refine ⟨y + y', add_mem hy hy', ?_⟩
  exact (congrArg₂ (· + ·) e e').trans (map_add (MvPolynomial.map B.embLL) y.1 y'.1).symm

theorem rowVal_smul {u : B.Word} {a : I.ι} (r : 𝓞 B.LL) {G : (I.per l u a).Mt} (h : RowVal I l u a G) :
    RowVal I l u a (B.embLL (r : B.LL) • G) := fun c => by
  obtain ⟨y, hy, e⟩ := h c
  refine ⟨r • y, Submodule.smul_mem _ r hy, ?_⟩
  exact (congrArg (B.embLL (r : B.LL) • ·) e).trans ((mapS B.embLL).map_smulₛₗ (r : B.LL) y.1).symm


def mtE (h : I.Ok) (u : B.Word) (a : I.ι) :
    MtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL ≃ₗ[ℂ] (I.per l u a).Mt :=
  mtEquiv (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.Ps u (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ _ => 0) B.embLL (tilOk I h u a).2.2


theorem span_toMtP (a : I.ι) : Submodule.span ℂ (Set.range fun z : MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps =>
    toMtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL z.1) = ⊤ :=
  span_toMtP_gen (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (base_fields_primes_ok B X).1 B.embLL




open Classical in

def reRows {C : Cols B} (W : RowsRest B C) (M : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (W.Amb μ))
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] W.Amb C.mu0) (eT : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] W.Amb μ) : RowsRest B C :=
  { GaloisStage.adapt W with
    Mtilde := M
    eMt0 := e0
    eMtTw := eT
    perCol := fun u μ φ F =>
      if h : μ = C.mu0 then (C.mem u).P.PtilCol (W.eMu u φ).1 ((e0 u).symm (cast (congrArg W.Amb h) F))
      else (C.PTw u μ).PtilCol (C.e0Tw u μ (W.eMu u φ).1) ((eT u μ).symm F)
    perCol_base_eq_PtilCol := fun u φ F => by
      rw [dif_pos rfl]
      rfl
    perCol_tie := fun u μ h φ F => dif_neg h }





theorem exists_ne_zero {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (M : Rows.OLat O φ V) : ∃ v ∈ M.carrier, v ≠ 0 := by
  classical
  by_contra H
  push Not at H
  have h1 : ∀ v ∈ M.gen, v = 0 := fun v hv => H v ⟨fun x => if x = v then 1 else 0, by
    rw [Finset.sum_eq_single v (fun x _ hx => by simp [hx]) (fun h => absurd hv h)]
    simp⟩
  have h2 : Submodule.span ℂ (M.gen : Set V) = ⊥ := Submodule.span_eq_bot.2 h1
  exact bot_ne_top (h2.symm.trans M.span_top)



end GlobalTheory.PerQ.Model

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdEmbEvz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartIndexInjectiveOffLastStep

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ClassPtReps
variable {D : D7}

theorem hasMat_iff (h : GA D D.sp.X') (y) :
    GlobalTheory.Core.Rk.Top.HasMat h y ↔ h ∈ GfC D.sp.X' ∧ finM D.sp.X' (Formalism.L2.Forms.rankP D) h = y.1 := by
  have key : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j =
      finM D.sp.X' (Formalism.L2.Forms.rankP D) h (finCongr (Formalism.L2.Forms.rankP D) i) (finCongr (Formalism.L2.Forms.rankP D) j) := by
    intro i j
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Matrix.ext fun i j => ?_⟩
    have := h2 ((finCongr (Formalism.L2.Forms.rankP D)).symm i) ((finCongr (Formalism.L2.Forms.rankP D)).symm j)
    rw [key] at this
    simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j => by rw [key, h2]⟩

theorem nontrivial_finAdeles : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial

theorem inclE_inj : Function.Injective
    (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI := nontrivial_finAdeles (D := D)
  exact Formalism.UG.P.inclE_injective D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem bc_inclE_inj {n : ℕ} : Function.Injective
    (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
      GL (Fin n) D.host.E → GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => inclE_inj (D := D) ?_)
  have h2 := congrArg (fun g : GL (Fin n) _ => g.val i j) hab
  simpa [Formalism.UG.bc] using h2

theorem eq_one_of_GQ {V : HSp D} {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V rfl γ = 1) : γ = 1 := by
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  have h2 : finM V rfl γ = δ.1.map (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl, Matrix.map_map]
    rfl
  have hδ1 : δ.1 = 1 := by
    apply Matrix.map_injective (inclE_inj (D := D))
    beta_reduce
    rw [← h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  apply Subtype.ext
  apply Units.ext
  show mt V γ = 1
  rw [e', hδ1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_GQ' {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V hn γ = 1) : γ = 1 := by
  subst hn
  exact eq_one_of_GQ hγ h1

theorem finGLHom_injOn {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ₁ γ₂ : GA D V} (h1 : γ₁ ∈ GQ V) (h2 : γ₂ ∈ GQ V)
    (e : GlobalTheory.ClassSumLevel.finGLHom V hn γ₁ = GlobalTheory.ClassSumLevel.finGLHom V hn γ₂) : γ₁ = γ₂ := by
  have h3 : γ₁⁻¹ * γ₂ ∈ GQ V := mul_mem (inv_mem h1) h2
  have h4 : finM V hn (γ₁⁻¹ * γ₂) = 1 := by
    have := congrArg Units.val (show GlobalTheory.ClassSumLevel.finGLHom V hn (γ₁⁻¹ * γ₂) = 1 by rw [map_mul, map_inv, e, inv_mul_cancel])
    exact this
  have := eq_one_of_GQ' hn h3 h4
  rw [← mul_inv_cancel_left γ₁ γ₂, this, mul_one]

theorem card_eq_of_lift {G A : Type} [Group G] (H : Subgroup G) (p : G → Prop) (q : A → Prop) (ρ : A → G) (hρ : ∀ a, ρ a ∈ H)
    (hpq : ∀ a, p (ρ a) ↔ q a) (hi : ∀ a b, ρ a = ρ b → a = b) (hs : ∀ γ ∈ H, ∃ a, ρ a = γ) :
    Nat.card {γ : H // p γ.1} = Nat.card {a // q a} := by
  refine (Nat.card_eq_of_bijective (fun a : {a // q a} => (⟨⟨ρ a.1, hρ a.1⟩, (hpq _).2 a.2⟩ : {γ : H // p γ.1}))
    ⟨fun a b hab => Subtype.ext (hi _ _ (congrArg (fun x : {γ : H // p γ.1} => x.1.1) hab)), fun γ => ?_⟩).symm
  obtain ⟨a, ha⟩ := hs γ.1.1 γ.1.2
  exact ⟨⟨a, (hpq a).1 (ha ▸ γ.2)⟩, Subtype.ext (Subtype.ext ha)⟩

open scoped ComplexOrder in
set_option maxHeartbeats 2000000 in

theorem isReps_of_level (V : HSp D) {n : ℕ} (hn : V.rank = n) (hV : ∀ τ, (gramAt D V τ).PosDef) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → Formalism.UG.UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (h : cl → GA D V) (hf : ∀ c, h c ∈ GfC V)
    (hh : ∀ c, finM V hn (h c) = (yc c).1.1) (U : Subgroup (GA D V))
    (mem : ∀ x, x ∈ U ↔ x ∈ GfC V ∧ x ∈ GlobalTheory.ClassSumLevel.levG V hn S) :
    IsReps V U h ∧ ∀ c, stabOrd U (h c) = Nat.card {δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)) //
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 ∈
        S.U.map (MulAut.conj (yc c).1).toMonoidHom} := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.1
  haveI := hT.2.2.2.2.1
  have hinf : ∀ k ∈ GinfC V, k ∈ GlobalTheory.ClassSumLevel.levG V hn S := fun k hk =>
    ⟨1, (GlobalTheory.ClassSumLevel.finM_eq_one_of_mem_GinfC V hn hk).symm⟩
  have split : ∀ k ∈ GlobalTheory.ClassSumLevel.levG V hn S, ∃ a ∈ GinfC V, ∃ κ ∈ U, k = a * κ := by
    intro k hk
    obtain ⟨a, ha, κ, hκ, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
    refine ⟨a, ha, κ, (mem κ).2 ⟨hκ, ?_⟩, rfl⟩
    have := mul_mem (inv_mem (hinf a ha)) hk
    rwa [inv_mul_cancel_left] at this
  have hex := GlobalTheory.ClassSumLevel.existsUnique_class V hn S yc hy h hh
  refine ⟨⟨fun x hx => ((mem x).1 hx).1, ?_, ?_, hf, fun g => ?_, fun c c' γ hγ k hk κ hκ e => ?_⟩, fun c => ?_⟩
  · have hc := GlobalTheory.ClassSumLevel.isCompact_levG V hn S hV
    have hcl : IsClosed (GfC V : Set (GA D V)) := by
      have e : (GfC V : Set (GA D V)) = {g | ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g} := by
        ext g
        exact ⟨fun hg => congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (V := V) ⟨g, hg⟩), fun hg => by
          have hg' : ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g := hg
          rw [← hg']
          exact (GlobalTheory.AutMult.toFin V g).2⟩
      rw [e]
      exact isClosed_eq (continuous_subtype_val.comp (GlobalTheory.AutMult.continuous_toFin V)) continuous_id
    have e : (U : Set (GA D V)) = (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) ∩ (GfC V : Set (GA D V)) :=
      Set.ext fun x => (mem x).trans and_comm
    rw [e]
    exact hc.inter_right hcl
  · have e : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) :=
      Set.ext fun x => ⟨fun hx => ((mem x.1).1 (Subgroup.mem_subgroupOf.1 hx)).2,
        fun hx => Subgroup.mem_subgroupOf.2 ((mem x.1).2 ⟨x.2, hx⟩)⟩
    rw [e]
    exact (GlobalTheory.ClassSumLevel.isOpen_levG V hn S).preimage continuous_subtype_val
  · obtain ⟨c, ⟨γ, hγ, k, hk, e⟩, -⟩ := hex g
    obtain ⟨a, ha, κ, hκ, rfl⟩ := split k hk
    exact ⟨γ, hγ, c, a, ha, κ, hκ, by rw [e]; simp only [mul_assoc]⟩
  · obtain ⟨c₀, -, hu⟩ := hex (h c')
    have h1 := hu c ⟨γ, hγ, k * κ, mul_mem (hinf k hk) ((mem κ).1 hκ).2, by rw [e]; simp only [mul_assoc]⟩
    have h2 := hu c' ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩
    exact h1.trans h2.symm
  · have hh' : GlobalTheory.ClassSumLevel.finGLHom V hn (h c) = (yc c).1 := Units.ext (hh c)
    have key : ∀ γ : GA D V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔
        GlobalTheory.ClassSumLevel.finGLHom V hn γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom := by
      intro γ
      have e1 : (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔ (h c)⁻¹ * γ * h c ∈ GlobalTheory.ClassSumLevel.levG V hn S := by
        constructor
        · rintro ⟨k, hk, κ, hκ, e⟩
          rw [mul_assoc, e, mul_assoc, inv_mul_cancel_left]
          exact mul_mem (hinf k hk) ((mem κ).1 hκ).2
        · intro hz
          obtain ⟨a, ha, κ, hκ, e⟩ := split _ hz
          exact ⟨a, ha, κ, hκ, by rw [mul_assoc, ← e, mul_assoc, mul_inv_cancel_left]⟩
      rw [e1, GlobalTheory.ClassSumLevel.mem_levG_iff, map_mul, map_mul, map_inv, hh']
      constructor
      · intro hz
        refine ⟨_, hz, ?_⟩
        show (yc c).1 * _ * (yc c).1⁻¹ = _
        group
      · rintro ⟨κ, hκ, e⟩
        have e' : (yc c).1 * κ * (yc c).1⁻¹ = GlobalTheory.ClassSumLevel.finGLHom V hn γ := e
        rw [← e', show (yc c).1⁻¹ * ((yc c).1 * κ * (yc c).1⁻¹) * (yc c).1 = κ by group]
        exact hκ
    have hr : ∀ δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)), ∃ γ ∈ GQ V,
        GlobalTheory.ClassSumLevel.finGLHom V hn γ =
          Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 := fun δ =>
      GlobalTheory.ClassSumLevel.exists_GQ_of_mem_ratPts V hn ⟨δ.1, δ.2, rfl⟩
    choose ρ hρ eρ using hr
    unfold stabOrd
    refine card_eq_of_lift (GQ V) (fun γ => ∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) _ ρ hρ (fun δ => (key _).trans (by rw [eρ])) (fun a b e => ?_) fun γ hγ => ?_
    · exact Subtype.ext (bc_inclE_inj (D := D) ((eρ a).symm.trans ((congrArg _ e).trans (eρ b))))
    · obtain ⟨δ, hδ, e⟩ := GlobalTheory.ClassSumLevel.finGLHom_mem_ratPts V hn hγ
      exact ⟨⟨δ, hδ⟩, finGLHom_injOn hn (hρ ⟨δ, hδ⟩) hγ ((eρ ⟨δ, hδ⟩).trans e)⟩

set_option maxHeartbeats 1000000 in

theorem isReps_stabOrd_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J _ j _ _ P t r a k tl Ch₀ A ι w _ UT ε hpin bad K eW _ _ _ hLev _ h hh
  have mem : ∀ x, x ∈ UT ↔ x ∈ GfC (I.rec7 l Z).sp.X' ∧
      x ∈ GlobalTheory.ClassSumLevel.levG (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z)) K.lev := by
    intro x
    refine ((hpin.lev x).trans (hLev.1 x)).trans ⟨?_, ?_⟩
    · rintro ⟨κ, hκ⟩
      exact ⟨hκ.1, κ, ((hasMat_iff x _).1 hκ).2.symm⟩
    · rintro ⟨h1, κ, hκ⟩
      exact ⟨κ, (hasMat_iff x _).2 ⟨h1, hκ.symm⟩⟩
  have H := isReps_of_level (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z))
    (GlobalTheory.RepsObj.gramAt_posDef (D7.X'_posDef _) (I.rec7 l Z).sp.X'_sig) K.lev K.y K.y_bij h (fun c => (hh c).1)
    (fun c => ((hasMat_iff _ _).1 (hh c)).2) UT mem
  refine ⟨H.1, fun c => (H.2 c).trans ?_⟩
  exact (Nat.card_congr ((MonoidHom.ofInjective (K.stabI_inj c)).toEquiv.trans
    (Equiv.subtypeEquivRight (K.stabI_range c)))).symm

end GlobalTheory.ClassPtReps
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_space_moved_level_class_points_representatives : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  atlas_forward_decl GlobalTheory.ClassPtReps.isReps_stabOrd_top
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TopInv

theorem multT_right {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (x : (⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) →ₗ[ℂ] GA D V → ℂ) (hx : x ∈ MultT θ M J χ)
    (v : ⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) : ∀ k ∈ J, ∀ g, x v (g * k) = χ k * x v g := by
  rw [mem_multT] at hx
  intro k hk g
  have key : ∀ T ∈ Mult θ M J χ, ∀ w, T w (g * k) = χ k * T w g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hT.lev w k hk g
    | zero => intro w; simp
    | add T T' _ _ h h' => intro w; simp [h, h', mul_add]
    | smul c T _ h => intro w; simp [h]; ring
  obtain ⟨T, rfl⟩ : ∃ T, x = PiTensorProduct.lift T := ⟨_, (PiTensorProduct.lift.apply_symm_apply x).symm⟩
  rw [LinearEquiv.symm_apply_apply] at hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w => simp [key _ hx w]; ring
  | add a b ha hb => simp [ha, hb, mul_add]

theorem rd_right {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.AdForm.rd_charts I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ0 * (A.h j b c * k0) * κ0 * κ.1 = γ0 * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd γ0 hγ0 c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

end GlobalTheory.AdForm.TopInv

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.AdForm.TopInv.law_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  intro B X I hOk hP l Z u G _ _ Pl0 Tt F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hT bad K eW hRd heW hbT hLev htl n hn ψ hψ f v y β x κ hκ
  subst hn
  unfold PinChL at hCh
  have hm : (I.rec7 l Z).R.m ≤ B.R.m := le_rfl
  rw [hT.eT, trc_single_apply, trc_single_apply]
  have hκ' := (hT.lev κ).1 hκ
  obtain ⟨κ', hκ'm⟩ := (hLev.1 κ).1 hκ'
  have hchi := hLev.2 κ κ' hκ'm
  have hx := f.2
  dsimp only [CXP] at hx
  have hr := multT_right _ _ _ _ _ hx v
  have hf := hr _ hκ' (x * g.bT)
  have e : x * g.bT * (g.bT⁻¹ * κ * g.bT) = x * κ * g.bT := by group
  rw [e] at hf
  obtain ⟨hU, hchiU, hnorm⟩ := (GlobalTheory.AdForm.rd_emb_evz I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hT.emb bad K hRd (ι _ β)).1 (GlobalTheory.AdForm.LevChiTop.chi_pow_of_levG K hLev) κ κ' hκ'm
  have hψF : ψ ∈ (I.fm l u a).Fi _ := ((hCh.ram _ hm ψ).1 hψ).1.1
  have hemb : (g.oT _ rfl).emb (x * κ, 1) = (g.oT _ rfl).emb (x, 1) * ((g.oT _ rfl).emb.comp (MonoidHom.inl _ _)) κ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hq : ∀ z, k.rd (I.rec7 l Z).R.m β ψ y z = A.rd R.θ _ hm (ι _ β) ψ y z := fun z => congrFun (hCh.rdq _ hm β ψ y) z
  have hr2 : A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1) * ((g.oT (I.rec7 l Z).R.m rfl).emb.comp (MonoidHom.inl _ _)) κ) = ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1)) :=
    rd_right I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hm ψ hψF _ y _ ⟨_, hU⟩
  have hc : ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) = ((K.lev.chi κ' : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hchiU
  rw [hemb, hq, hq, hr2, hc, hf, hchi]
  have h1 : star ((K.lev.chi κ' : ℂˣ) : ℂ) * ((K.lev.chi κ' : ℂˣ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]; simp
  linear_combination (ε * f.1 v (x * g.bT) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1))) * h1
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriod_law_movedLevel : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  atlas_forward_decl GlobalTheory.AdForm.TopInv.law_top
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_translate_real_point_read_by_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  atlas_forward_decl GlobalTheory.AdForm.TopTranslate.top_translate
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvzVal

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_eq_lamT_hcW {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem evz_mem_valC : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (ψ : ColT I l u a B.R.m), ψ ∈ (I.fm l u a).Fi B.R.m → ∀ c, (fun y : FrN (I.rec7 l Z) (B.R.N B.R.m) => (I.per l u a).evz ψ c ⟨y.1, y.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m) := by
  intro B X I hI hP l Z u a ψ hψ c
  have h1 := (hψ ((I.perIn u a).tilC c)).1
  have h2 := GlobalTheory.Mem.Col2.Law.tr_mem (I.stp u a B.R.m) B.fields.emb B.embLL _ (I.perIn u a).b0
    ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) h1
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 h2
  rw [lamT_eq_lamT_hcW I l Z u B.R.m]
  exact ⟨P, hP, funext fun y => congrFun e ⟨y.1, y.2⟩⟩

end GlobalTheory.EvzVal

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

open Formalism.L2.Col in

theorem tailTop_eq_of_pin : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hRP heW hbT hLev hG h hh hst G' hG' n hn ψ hψ f
  subst hn
  have hC : PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK := hCh
  have hIs : A.Is := hC.is
  have hψF : ψ ∈ (I.fm l u a).Fi B.R.m := ((hC.ram B.R.m le_rfl ψ).1 hψ).1.1
  have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := N_m_succ B.R

  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = (I.per l u a).lowerMap ((I.per l u a).evz ψ) := ⟨_, rfl⟩
  have hlow : ∀ c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)),
      Lz c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) y :=
    fun c y => hLz ▸ (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.2.2 a _ c y
  have heL : ∀ c, eW Lz c = fun y => lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) ⟨y.1, y.2⟩ := by
    intro c; funext y
    rw [heW Lz c y ⟨y.1, y.2⟩ rfl]
    exact hlow c ⟨y.1, y.2⟩

  have hw : ∀ c, eW Lz c ∈ LinearMap.range j := by
    intro c
    rw [hj.range]
    have hv0 := GlobalTheory.EvzVal.evz_mem_valC I hI hP l Z u a ψ hψF c
    have hv1 := (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.1.1 _ hv0
    obtain ⟨Pp, hPp, hEq⟩ := hv1
    rw [heL c]
    exact ⟨Pp, hPp, funext fun y => congrFun hEq ⟨y.1, y.2⟩⟩
  obtain ⟨G'', hR'', htl⟩ := hG ψ f
  have hper : (I.per l u a).Ptil ψ (G' f) = tl ψ f := by
    rw [htl]
    have := GlobalTheory.Fam.Check.ReadsG.period_eq K eW j g.bT (hG' f) hR'' Lz hw
    rw [hLz] at this
    exact this

  have hsum : ∀ β : k.Ch B.R.m, ∑ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
      (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) = ε * tl ψ f := by
    intro β
    have hev : ∀ c y, A.rd R.θ B.R.m le_rfl (ι B.R.m β) ψ y ((g.oT B.R.m rfl).emb (h c, 1)) = (I.per l u a).evz ψ c y :=
      fun c y => (GlobalTheory.AdForm.rd_emb_evz I hI hP l Z u a Ch₀ A hIs R.θ hX.inf _ hTop.emb bad K hRP (ι B.R.m β)).2 ψ hψF c (h c) (hh c) y
    have hterm : ∀ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
        (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) =
        ε * (I.per l u a).period (eW.symm (Pi.single c (eW Lz c))) (G' f) := by
      intro c
      have hne : (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := (I.fm l u a).stabilizer₂ c)).ne'
      have e2 : (fun z : FrN (I.rec7 l Z) (B.R.N B.R.m) => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1))) =
          fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩ := by
        funext z
        exact (congrFun (hC.rdq B.R.m le_rfl β ψ _) _).trans (hev c _)
      rw [e2, ellTop_apply, hst c, heL c]
      field_simp
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum]
    have e3 : ∑ c, Pi.single c (eW Lz c) = eW Lz := Finset.univ_sum_single _
    rw [e3, LinearEquiv.symm_apply_apply, ← hper, hLz]
    rfl
  have hsub : Subsingleton (k.Ch B.R.m) :=
    ⟨fun β β' => hC.live.inj B.R.m ((GlobalTheory.AdForm.TwTest.subsingleton_top hIs).elim _ _)⟩
  rw [hTop.cP]
  have htail : ∀ hm, (tupOf R P u g t r k tl).tail _ hm ψ f = tl ψ f := fun _ => rfl
  rw [htail]
  refine (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (Finset.sum_congr rfl fun β _ => hsum β)).trans ?_
  have e1 : ∀ {α : Type} (inst : Fintype α), (∀ a b : α, a = b) → α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = x := by
    intro α inst hs a x
    haveI : Unique α := ⟨⟨a⟩, fun b => hs _ _⟩
    exact Fintype.sum_unique _
  have e0 : ∀ {α : Type} (inst : Fintype α), IsEmpty α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = 0 := by
    intro α inst hE x
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rcases isEmpty_or_nonempty (k.Ch B.R.m) with hE | hne
  · have h0 : ψ = 0 := by
      funext c
      obtain ⟨β, -⟩ := hC.live.last (A.chOf B.R.m c)
      exact (hE.false β).elim
    have h1 : tl ψ f = 0 := by
      rw [← hper, h0]
      show ((I.per l u a).period ((I.per l u a).lowerMap ((I.per l u a).evz 0))) (G' f) = 0
      simp only [map_zero, LinearMap.zero_apply]
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e0 _ hE _)).trans (by rw [h1]; ring)
  · obtain ⟨β₀⟩ := hne
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e1 _ (fun a b => hsub.elim a b) β₀ _)).trans (by ring)

end GlobalTheory.AdForm
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  atlas_forward_decl GlobalTheory.AdForm.tailTop_eq_of_pin
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem exists_clsT_of_pinTop : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  intro B X I hI hPins l Z u G iG iGf Pl0 T F Ks iK iNK iA R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  choose h hh using fun c : (I.fm l u a).clsP => GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
  choose G' hG' using hG 0
  obtain ⟨hrep, hst⟩ := GlobalTheory.T.last_space_moved_level_class_points_representatives I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh
  refine ⟨clsTop R g P r k tl s J UT h eW ε G', hrep, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.lastPeriod_law_movedLevel I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  · intro n hn f v β c x hx
    show trc (k.eT n hn β) (f.1 v) (h c * x) = ellTop R P eW ε G' c f (J v x)
    rw [hTop.eT n hn β, trc_single_apply, ellTop_apply, GlobalTheory.T.form_translate_real_point_read_by_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh G' (fun f => (hG' f).1) f v c x hx]
    ring
  · exact GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh hst G' (fun f => (hG' f).1)

end GlobalTheory.AdForm
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lastPeriod_classData_of_lastStep : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  atlas_forward_decl GlobalTheory.AdForm.exists_clsT_of_pinTop
end

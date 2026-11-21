import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

def dat3 (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat3 D (A3.comap f μ) Ks where
  toRealDat := dat2 (A := A3.A) f μ R.toRealDat mu tw
  plI := R.plI
  SF := R.SF
  phs := R.phs
  lam3 i t := R.lam3 i (f t)

def bare3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) : Face3 D A3 where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem isInert (h : R.IsInert) : (dat3 f μ R mu tw).IsInert := by
  exact ⟨⟨h.tie.plI_inj, fun t Q => h.tie.okI (f t) Q⟩, h.onto, fun t => h.hR (f t), fun i t => h.hL i (f t), h.SF⟩

set_option maxHeartbeats 2000000 in

theorem pThmB (h : R.PThmB) : (dat3 f μ R mu tw).PThmB := by
  intro t p x hx
  exact h (f t) p x hx

set_option maxHeartbeats 2000000 in

theorem isScal (h : R.IsScal (bare3 _ P0 ψ0 P1 ψ1)) (hB : R.PThmB) : (dat3 f μ R mu tw).IsScal (bare3 _ P0 ψ0 P1 ψ1) where
  lam0 i t := h.lam0 i (f t)
  kap κ hκ hne := by
    obtain ⟨t, p, hp, hl⟩ := hne
    exact Lift.IsKap.unique (pThmB mu tw hB) hκ t p hp hl
  off := h.off
  abs0 i t := h.abs0 i (f t)
  abs := h.abs
  tup i t := h.tup i (f t)

structure NewTup (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop where

  sub : tw ⊆ R.twPl

  conj : ∀ w, Formalism.DivisionValues.conjPl w ∈ tw ↔ w ∈ tw

  on : ∀ w ∈ tw, f (mu w) = R.mu w

  off : ∀ w, w ∉ tw → mu w = μ

  used : ∀ t, t = μ ∨ ∃ w, mu w = t

variable {mu tw} in

theorem isTup (hf : Function.Injective f) (h : R.IsTup) (n : NewTup R mu tw) : (dat3 f μ R mu tw).IsTup where
  mu_off := n.off
  mu_used := n.used
  mu_ne w hw heq := by
    change mu w = μ at heq
    apply h.mu_ne w (n.sub hw)
    rw [← n.on w hw, heq]
    rfl
  mu_conj w := by
    change mu (Formalism.DivisionValues.conjPl w) = mu w
    by_cases hw : w ∈ tw
    · apply hf
      have hc : Formalism.DivisionValues.conjPl w ∈ tw := (n.conj w).2 hw
      rw [n.on _ hc, n.on w hw]
      exact h.mu_conj w
    · have hc : Formalism.DivisionValues.conjPl w ∉ tw := fun hc => hw ((n.conj w).1 hc)
      rw [n.off _ hc, n.off w hw]
  mu_on w hw := by
    obtain ⟨ψw, Qw, h1, h2⟩ := h.mu_on w (n.sub hw)
    refine ⟨ψw, Qw, h1, ?_⟩
    change R.xiH (f (mu w)) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw
    rw [n.on w hw]
    exact h2

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem restricted_character_data_valid (hf : Function.Injective f) (h : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (e : R.toRealDat.ExAt) (hB : R.PThmB)
    (n : NewTup R mu tw) : (dat3 f μ R mu tw).WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1) where
  base := baseW mu tw hf h.base e
  inert := isInert mu tw h.inert
  fullY t := h.fullY (f t)
  fullX t := h.fullX (f t)
  fullP i t := h.fullP i (f t)
  scal := isScal mu tw h.scal hB
  tup := isTup hf h.tup n
  phase := h.phase
  allPl := h.allPl

set_option maxHeartbeats 2000000 in

theorem keep {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Keep (A3 := A3.comap id (f μ)) R.toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG) :
    Keep (A3 := A3.comap f μ) (dat3 f μ R mu tw).toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG where
  std := h.std
  signs := h.signs
  frames := h.frames
  beta := h.beta
  prX := h.prX
  grp := h.grp
  psi := h.psi
  guard := ⟨fun t => h.guard.1 (f t), fun t => h.guard.2 (f t)⟩
  valKs := h.valKs
  frameKs := h.frameKs
  levKs := h.levKs

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem pins (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (hB : R.PThmB) (n : NewTup R mu tw) : Pins (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) cG where
  char := restricted_character_data_valid hf h.char e hB n
  keep := keep mu tw h.keep
  phs := h.phs
  trSem := h.trSem

end GlobalTheory.Mem.R3.Res

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {s : ℕ}

theorem volume_le_of_trivial_first_pair (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) :
    X.goodPartComplexPoints (cvOf3 A3 P0 ψ0 P1 ψ1) false j t ≤ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t := by
  have H := lift_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  have e0 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 P0 ψ0 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA P0 ψ0) rfl
  have e2 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 ⊥ 1 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA ⊥ 1) rfl
  have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
    goodAt_bot A3.fam3.F.X _
  rw [e1] at e2
  exact e0.le.trans ((H.range_le A3.fam3.F.X P0 ψ0⁻¹).trans e2.ge)

theorem exists_crd (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 ⊥ 1 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) (w : X.W j)
    (hw : LinearMap.adjoint (X.θ' j t) w ∈ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t) :
    ∃ c, lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) c = LinearMap.adjoint (X.θ' j t) w := by
  have hrat := lift_rationality_of_equivariance (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK hJ hRZ hU hG false j t
  have hu := hrat.ge (Submodule.mem_inf.2 ⟨⟨w, rfl⟩, hw⟩)
  refine (Submodule.span_le (p := LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)))).2 ?_ hu
  rintro _ ⟨x, rfl⟩
  exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩

theorem range_w0C_le (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (hL0 : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0)
    (hA : X.ThmAop false) (hW : X.PartsW false) (hp : ∀ j t p v, 0 < X.lam j t p v) (j : Fin m) (t : T) :
    LinearMap.range (X.w0C false j) ≤ LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) := by
  have hup := upper_level_lift_at_lower_type hok hK hJ hU hG hL0 j t
  refine (hW j).2.ge.trans (iSup_le fun p w hw => ?_)
  obtain ⟨c, hc⟩ := exists_crd (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK (fun j t x y => hJ j t x y) hRZ hU hG j t w
    (volume_le_of_trivial_first_pair hok hK hJ hU hG j t (hup ⟨w, hw.2, rfl⟩))
  have hl : ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp j t p _).ne'
  have h1 : X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t c = ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) • w :=
    (X.tC_eq _ false j t c).trans ((congrArg (X.θ' j t) hc).trans (hA j t p w hw))
  refine ⟨((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ)⁻¹ • c, (map_smul _ _ _).trans ?_⟩
  rw [h1, smul_smul, inv_mul_cancel₀ hl, one_smul]

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem pHecke (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1)) : (dat3 f μ R mu tw).PHecke (bare3 _ P0 ψ0 P1 ψ1) := by
  obtain ⟨⟨hE, h1⟩, hW, h2⟩ := h
  exact ⟨⟨fun t => hE (f t), fun t => h1.intw (f t), h1.comm, h1.parts⟩,
    fun j t => hW j (f t), fun j t => h2.intw j (f t), h2.comm, h2.parts⟩

set_option maxHeartbeats 2000000 in

theorem liftOnto (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1))
    (ho : ∀ hW, HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW) :
    ∀ hW, HeckeIntertwiningLifts (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW := by
  classical
  intro hW' h'
  obtain ⟨hW0, h0⟩ := h.2
  let hW : ∀ j t, ((A3.comap id (f μ)).liftI j t).OpIx → Module.End ℂ ((R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)).W j) :=
    fun j => Function.update (hW0 j) (f μ) (hW' j μ)
  have e : ∀ j, hW j (f μ) = hW' j μ := fun j => Function.update_self _ _ _
  have hh : HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW := by
    refine ⟨fun j t => ?_, fun j => ?_, fun j p => ?_⟩
    · by_cases ht : t = f μ
      · subst ht
        intro i u
        rw [e j]
        exact h'.intw j μ i u
      · have e' : hW j t = hW0 j t := Function.update_of_ne ht _ _
        rw [e']
        exact h0.intw j t
    · exact (e j).symm ▸ h'.comm j
    · exact (h'.parts j p).trans (congrArg (fun z => Formalism.L2.Col.eigSum z _) (e j).symm)
  intro j
  have := ho hW hh j
  exact (e j) ▸ this

set_option maxHeartbeats 2000000 in

theorem pLevW {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    (dat3 f μ R mu tw).PLevW (bare3 _ P0 ψ0 P1 ψ1) := by
  have hR := complex_data_conditions_base_level_of_primitive_links hok hs hC h
  intro j
  have h1 := range_w0C_le hok hR.kFormL hR.jIsoL hR.ratZ hR.gUnitL hR.gEquivL hR.lower_level_lift_type hR.thmAop hR.partsW h.posScal.2 j (f μ)
  have h2 := h.levW j
  apply le_antisymm
  · exact le_inf (h1.trans (le_iSup_of_le μ le_rfl)) (h2.le.trans inf_le_right)
  · refine le_trans (inf_le_inf_right _ (iSup_le fun t => ?_)) h2.ge
    exact le_iSup_of_le (f t) le_rfl

set_option maxHeartbeats 4000000 in

theorem primRows3 {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    PrimRows3 (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  heckeR t := h.heckeR (f t)
  heckeL j t := h.heckeL j (f t)
  hecke := pHecke mu tw h.hecke
  gUnit := h.gUnit
  gEquiv := ⟨fun t => h.gEquiv.1 (f t), fun j t => h.gEquiv.2 j (f t)⟩
  block := ⟨fun t => h.block.1 (f t), fun j t => h.block.2 j (f t)⟩
  rowTest := by
    obtain ⟨N, ψ, h1, h2⟩ := h.rowTest
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTest j := by
    obtain ⟨N, ψ, h1, h2⟩ := h.liftTest j
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTestB j := by
    obtain ⟨N, ψ, h1, h2, h3⟩ := h.liftTestB j
    exact ⟨N, ψ, h1, fun t => h2 (f t), h3⟩
  liftOnto := liftOnto mu tw h.hecke h.liftOnto
  pos b := by
    cases b
    · exact h.pos false
    · exact h.pos true
  posScal := ⟨h.posScal.1, fun i t => h.posScal.2 i (f t)⟩
  levE := h.levE
  h2P := ⟨h.h2P.1, fun t => h.h2P.2 (f t)⟩
  thmB := pThmB mu tw h.thmB
  sumE := h.sumE
  unif := h.unif
  mLat := h.mLat
  levW := pLevW mu tw hok hs hC h
  thmA i t := h.thmA i (f t)
  sumW := h.sumW
  scalConj := h.scalConj
  dimParts := h.dimParts

set_option maxHeartbeats 2000000 in

theorem intersectionNumber_baseChange (hf : Function.Injective f) (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : Holds R (bare3 _ P0 ψ0 P1 ψ1)) :
    Holds (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  prim := primRows3 mu tw h.ok h.sep hC h.prim
  aux := ⟨exAt (A := A3.A) mu tw h.aux.ex, h.aux.conj, h.aux.levelW, h.aux.integral⟩
  ok := (A3.comap id (f μ)).fam3.comap_ok_of_injective h.ok hf μ
  sep := h.sep

end GlobalTheory.Mem.R3.Res

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}

def plB (X : Stages) : X.B.places.Pl ≃ HeightOneSpectrum (𝓞 X.toD7.what₂.LL) := X.toD7.plEq

theorem plB_conj (w : X.B.places.Pl) : plB X (X.B.places.conj w) = Formalism.DivisionValues.conjPl (plB X w) := by
  have hc := plConjEq X.toD7
  exact hc w

def ConjStable (X : Stages) (Wt : Set X.B.places.Pl) : Prop := ∀ w ∈ Wt, X.B.places.conj w ∈ Wt

theorem ConjStable.symm_mem_iff {Wt : Set X.B.places.Pl} (h : ConjStable X Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    (plB X).symm (Formalism.DivisionValues.conjPl v) ∈ Wt ↔ (plB X).symm v ∈ Wt := by
  constructor
  · intro hv
    have e : X.B.places.conj ((plB X).symm (Formalism.DivisionValues.conjPl v)) = (plB X).symm v := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    rw [← e]
    exact h _ hv
  · intro hv
    have e : X.B.places.conj ((plB X).symm v) = (plB X).symm (Formalism.DivisionValues.conjPl v) := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← e]
    exact h _ hv

theorem tuOf_mono (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : tuOf I U' ⊆ tuOf I U := by
  intro τ hτ
  obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
  exact (mem_tuOf I).2 ⟨a, h ha, rfl⟩

def inclU (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : TupU I U' → TupU I U := TupF.incl (tuOf_mono I h)

theorem inclU_injective {U U' : Set I.ι} (h : U' ⊆ U) : Function.Injective (inclU I h) := by
  intro s t hst
  have hv : (inclU I h s).1 = (inclU I h t).1 := congrArg Subtype.val hst
  exact Subtype.ext hv

theorem ixOf_inclU {U U' : Set I.ι} (h : U' ⊆ U) (t : TupU I U') : ixOf I U (inclU I h t) = ixOf I U' t := rfl

variable {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem plB_mem_twPl (w : X.B.places.Pl) : plB X w ∈ z.R.twPl ↔ w ∈ Wt := by
  exact (z.mu w).1

theorem xi_mu {w : X.B.places.Pl} (hw : w ∈ Wt) : I.xi (ixOf I (usedOf I T Wt) (z.R.mu (plB X w))) = T.xiTw I.C w := by
  have hm := (z.mu w).2
  rw [if_pos hw] at hm
  exact hm

theorem mu_mem (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    (z.R.mu v).1 ∈ tuOf I (usedOf I T Wt') := by
  have hx := z.xi_mu (h hv)
  rw [Equiv.apply_symm_apply] at hx
  have hu : ixOf I (usedOf I T Wt) (z.R.mu v) ∈ usedOf I T Wt' := ⟨(plB X).symm v, hv, hx⟩
  have hm := (tup_mem_tuOf I).2 hu
  rwa [tup_ixOf] at hm

open Classical in

def resMu (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : TupU I (usedOf I T Wt') :=
  if hv : (plB X).symm v ∈ Wt' then ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))

open Classical in

def resTw (Wt' : Set X.B.places.Pl) : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :=
  z.R.twPl.filter fun v => (plB X).symm v ∈ Wt'

theorem mem_twPl (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.R.twPl ↔ (plB X).symm v ∈ Wt := by
  have hm := z.plB_mem_twPl ((plB X).symm v)
  rwa [Equiv.apply_symm_apply] at hm

theorem mem_resTw (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.resTw Wt' ↔ (plB X).symm v ∈ Wt' := by
  classical
  unfold resTw
  rw [Finset.mem_filter, z.mem_twPl]
  exact ⟨fun hv => hv.2, fun hv => ⟨h hv, hv⟩⟩

theorem inclU_resMu (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    inclU I (usedOf_mono I T h) (z.resMu h v) = z.R.mu v := by
  have e : z.resMu h v = ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ := dif_pos hv
  rw [e]
  rfl

theorem resMu_off (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∉ Wt') :
    z.resMu h v = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) := by
  exact dif_neg hv

theorem resMu_used (h : Wt' ⊆ Wt) (t : TupU I (usedOf I T Wt')) :
    t = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) ∨ ∃ v, z.resMu h v = t := by
  obtain ⟨τ, hτ | hτ⟩ := t
  · left
    exact Subtype.ext hτ
  · right
    obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
    obtain ⟨w, hw, hxa⟩ := ha
    refine ⟨plB X w, ?_⟩
    have hw' : (plB X).symm (plB X w) ∈ Wt' := by
      rw [Equiv.symm_apply_apply]
      exact hw

    have hau : a ∈ usedOf I T Wt := usedOf_mono I T h ⟨w, hw, hxa⟩
    obtain ⟨ta, hta⟩ : ∃ ta : TupU I (usedOf I T Wt), ta.1 = I.tup a :=
      ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 hau)⟩, rfl⟩
    have hix : ixOf I (usedOf I T Wt) ta = a := ixOf_eq I hta.symm
    have hs := z.xi_mu (h hw)
    have hxi : z.R.toLevCh.xiH ta = z.R.toLevCh.xiH (z.R.mu (plB X w)) := by
      rw [z.lev.xiH, z.lev.xiH, hix, hs, hxa]

    have he := z.lev.is.xi_inj hxi
    have e : z.resMu h (plB X w) = ⟨(z.R.mu (plB X w)).1, Or.inr (z.mu_mem h hw')⟩ := dif_pos hw'
    rw [e]
    apply Subtype.ext
    show (z.R.mu (plB X w)).1 = I.tup a
    rw [← he]
    exact hta

theorem muOf_res (h : Wt' ⊆ Wt) : MuOf X I T Wt' (z.resMu h) (z.resTw Wt') := by
  intro w
  have hpl : (plB X).symm (X.toD7.plEq w) = w := (plB X).symm_apply_apply w
  refine ⟨?_, ?_⟩
  · rw [z.mem_resTw h, hpl]
  · by_cases hw : w ∈ Wt'
    · rw [if_pos hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∈ Wt' := by
        rw [hpl]
        exact hw
      rw [← ixOf_inclU (usedOf_mono I T h), z.inclU_resMu h hw']
      exact z.xi_mu (h hw)
    · rw [if_neg hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∉ Wt' := by
        rw [hpl]
        exact hw
      rw [z.resMu_off h hw', ixOf_mu0F]

      have hb := z.lev.is.xi_base
      rw [z.lev.xiH, ixOf_mu0F] at hb
      exact hb

set_option maxHeartbeats 1000000 in

def resR (h : Wt' ⊆ Wt) : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt') z.Xg z.tr) z.core.Q.c.F :=
  Res.dat3 (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (inclU I (usedOf_mono I T h))
    (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt')

set_option maxHeartbeats 1000000 in

theorem newTup (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Res.NewTup (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (f := inclU I (usedOf_mono I T h))
      (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') where
  sub v hv := (z.mem_twPl v).2 (h ((z.mem_resTw h v).1 hv))
  conj v := by
    rw [z.mem_resTw h, z.mem_resTw h]
    exact hc.symm_mem_iff v
  on v hv := z.inclU_resMu h ((z.mem_resTw h v).1 hv)
  off v hv := z.resMu_off h fun hv' => hv ((z.mem_resTw h v).2 hv')
  used t := z.resMu_used h t

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cx_zs_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) (κ lam e) : (reErr (reScal Y κ lam) e).zs = Y.zs := rfl

theorem cx_liftMat_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) : (reErr (reScal Y κ lam) e).liftMat cr b j t = Y.liftMat cr b j t := by
  have h : (reErr (reScal Y κ lam) e).liftMatC cr b j t = Y.liftMatC cr b j t := by
    unfold CxData.liftMatC
    rfl
  exact congrArg (kMat Bs.v0.embedding) h

theorem cx_Iw_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    ((reErr (reScal Y κ lam) e).data cr b).Iw j t w = (Y.data cr b).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M b j) (Formalism.DivisionValues.matLat M ((lv (fc Y.zs) b).Tl j t))) (cx_liftMat_scal Y cr κ lam e b j t)

theorem definiteComplexNonzeroIndexPlaces_rescale_errors {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : (reErr (reScal Y κ lam) e).W1 cr N w ↔ Y.W1 cr N w :=
  exists_congr fun j => or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _)))
    (or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _))) Iff.rfl)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} (Y : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
  (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc Dc' : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
  (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Sp' : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc' Zs))
  (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem cx_tC_face (j : Fin m) (t : T) :
    Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t := rfl

theorem cx_liftMat_face (j : Fin m) (t : T) :
    Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t :=
  congrArg (fun g => kMat A3.fam3.base3.v0.embedding (relMat (Y.w0C false j) g)) (cx_tC_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem cx_Iw_face (j : Fin m) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false).Iw j t w = (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M false j) (Formalism.DivisionValues.matLat M ((A3.side3 P0 ψ0 Y.zs).Tl j t)))
    (cx_liftMat_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem definiteSide_nonzeroIndexPlaces_any_columns_scale (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 K)) :
    Y.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') N w ↔ ∃ j : Fin m,
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 w ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) w ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨ N.F0 w j ≠ 0) ∨
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 (Formalism.DivisionValues.conjPl w) ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) (Formalism.DivisionValues.conjPl w) ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨
          N.F0 (Formalism.DivisionValues.conjPl w) j ≠ 0) := by
  refine exists_congr fun j => ?_
  rw [← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j, ← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j]
  have key : ∀ a b c d e f : Prop, (a ∨ b ∨ c ∨ d ∨ e ∨ f) ↔ (a ∨ c ∨ e) ∨ (b ∨ d ∨ f) := fun _ _ _ _ _ _ => by tauto
  exact key _ _ _ _ _ _

end Cx

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def NzAt (R : RealDat3 D A3 Ks) (F : Face3 D A3) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (s0Of R F).Iw j A3.A.μ0 w ≠ 0 ∨
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 (zsOf R F)).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 (zsOf R F)).Tl j A3.A.μ0) ≠ 0 ∨ F0 w j ≠ 0

set_option maxHeartbeats 1000000 in

theorem toCx3_upd_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc) = reErr (reScal (R.toCx3 F) (fun _ => kap) lam) err := rfl

set_option maxHeartbeats 1000000 in

theorem complexSide_nonzeroIndexPlaces_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (N : IndefNum A3.fam3.base3)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).W1 (reFace F Dc Sp Zsc).cr N w ↔
      ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  rw [e]
  exact (definiteComplexNonzeroIndexPlaces_rescale_errors (R.toCx3 F) _ _ _ _ N w).trans (definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc Dc F.Sp Sp F.Zsc Zsc N w)

set_option maxHeartbeats 1000000 in

theorem complexSide_nonzeroIndexPlaces_iff_self (R : RealDat3 D A3 Ks) (F : Face3 D A3) (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (R.toCx3 F).W1 F.cr N w ↔ ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) :=
  definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Dc F.Sp F.Sp F.Zsc F.Zsc N w

set_option maxHeartbeats 1000000 in

theorem nzAt_res {f : T' → T} {μ : T'} (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (Res.dat3 f μ R mu tw) (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w ↔ NzAt R (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w := Iff.rfl

set_option maxHeartbeats 1000000 in

theorem complexSide_numberContents_eq_scaleAtSubspaces (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (C CH : ℝ) :
    (((R.updS kap lam).withErr err).num (reFace F Dc Sp Zsc) C CH).F0 = (Zsc (zsOf R F)).F0 := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  have e2 : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs e).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have e3 : ∀ (F' : Face3 D A3) (s : DefSub A3.fam3.amb3), ((F'.fc s).Z.num C CH).F0 = (F'.Zsc s).F0 := fun _ _ => rfl
  exact (e3 (reFace F Dc Sp Zsc) _).trans (congrArg (fun s => (Zsc s).F0) e2)

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem _root_.GlobalTheory.Mem.R3.columnChoiceReferenceFace_eq_bareFaceTwoLevels (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    face0 X I hX U Xg tr = Res.bare3 (famR X I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) := rfl

set_option maxHeartbeats 2000000 in

def resGeo (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resR h).toRealDat fun _ => 1 :=
  Res.geoHalf (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') z.geo

set_option maxHeartbeats 2000000 in

theorem pins_resR (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) (hB : z.R.PThmB) :
    Pins (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact Res.pins (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I) (mu := z.resMu h) (tw := z.resTw Wt')
    (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e hB (z.newTup h hc)

set_option maxHeartbeats 2000000 in

theorem holds_resR (h : Wt' ⊆ Wt) (hH : Holds z.R z.F) : Holds (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) := by
  have hp := z.pins.char
  have hH' : Holds z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) := hH
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp hH' ⊢
  exact Res.intersectionNumber_baseChange (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I) (z.resMu h) (z.resTw Wt')
    (inclU_injective (usedOf_mono I T h)) hp hH'

set_option maxHeartbeats 2000000 in

theorem levOf_resR (h : Wt' ⊆ Wt) : LevOf X I (usedOf I T Wt') (z.resR h).toLevCh where
  is := Res.levCh_is (L := z.R.toLevCh) (inclU_injective (usedOf_mono I T h)) z.lev.is
  C := z.lev.C
  xiH t := z.lev.xiH (inclU I (usedOf_mono I T h) t)
  Pg := z.lev.Pg
  Q t := z.lev.Q (inclU I (usedOf_mono I T h) t)
  beta := z.lev.beta

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Res

section Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {ph : Fin D.R.m → ℂ}

set_option maxHeartbeats 2000000 in

def geoScal (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R kap lam err g.fw, g.bar, fun i => GlobalTheory.RealGeo.Upd.updO C R kap lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩

set_option maxHeartbeats 2000000 in

theorem inGeo_geoScal_iff (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.InGeo (geoScal g kap lam err) ↔ GlobalTheory.RealGeo.InGeo g :=
  ⟨fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩,
    fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩⟩

end Geo

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem baseW_scal {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {F : Face D A} (h : R.BaseW F) (k l) :
    (R.upd6 k l).BaseW F :=
  ⟨h.lev, ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE, h.models.HW,
      h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX, h.models.νV,
      h.models.νW, h.models.BV, h.models.order⟩, RealDat.weak_chain_of_scalar_update h.chain k l, RealDat.weak_theta_props_of_scalar_update h.thP k l⟩

set_option maxHeartbeats 2000000 in

theorem exAt_scal {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} (e : R.ExAt) (k l) : (R.upd6 k l).ExAt :=
  ⟨e.ItY, e.ItX, e.ioY, e.ioX, e.Th, e.ioP, e.thF, e.thG⟩

set_option maxHeartbeats 4000000 in

theorem nzAt_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (R.updS kap lam) F F0 j w ↔ NzAt R F F0 j w := by
  have e1 : (s0Of (R.updS kap lam) F).Iw j A3.A.μ0 w = (s0Of R F).Iw j A3.A.μ0 w :=
    cx_Iw_scal (R.toCx3 F) F.cr (fun _ => kap) lam R.err0 false j A3.A.μ0 w
  have e2 : zsOf (R.updS kap lam) F = zsOf R F := RealDat3.zs_updS kap lam
  unfold NzAt
  rw [e1]
  exact or_congr Iff.rfl (or_congr (not_congr (Eq.congr_left (congrArg (fun s =>
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 s).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 s).Tl j A3.A.μ0)) e2))) Iff.rfl)

def KapFixed (S : RealDat3 D A3 Ks) (κ : ℝ) : Prop :=
  Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
    ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0

open Classical in

def kapNew (S : RealDat3 D A3 Ks) : ℝ := if h : ∃ κ, KapFixed S κ then h.choose else S.kap

theorem kapNew_eq (S : RealDat3 D A3 Ks) {κ : ℝ} (h : KapFixed S κ) : kapNew S = κ := by
  have h' : ∃ κ, KapFixed S κ := ⟨κ, h⟩
  unfold kapNew
  rw [dif_pos h']
  obtain ⟨t, p, hp, hl⟩ := h.2
  exact Lift.IsKap.unique h'.choose_spec.1 h.1 t p hp hl

theorem kapNew_of_not (S : RealDat3 D A3 Ks) (h : ¬ ∃ κ, KapFixed S κ) : kapNew S = S.kap := dif_neg h

theorem kapNew_of_thmB (S : RealDat3 D A3 Ks) (h : S.PThmB) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · exact kapNew_eq S ⟨h, h'.choose_spec.2⟩
  · exact kapNew_of_not S h'

theorem kapNew_of_scal (S : RealDat3 D A3 Ks) (h : S.scal_kap) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · obtain ⟨κ, hκ⟩ := h'
    exact (kapNew_eq S hκ).trans (h κ hκ.1 hκ.2).symm
  · exact kapNew_of_not S h'

set_option maxHeartbeats 2000000 in

theorem isScal_kapNew (S : RealDat3 D A3 Ks) (F : Face3 D A3) (h0 : S.eigenvalue_at_base_of_scalar) (h1 : S.scal_off F) (h2 : S.zero_part_eigenvalue_convention F)
    (h3 : S.scal_abs F) (h4 : S.scal_tup) : (S.updS (kapNew S) S.lam3).IsScal F := by
  refine ⟨h0, fun κ h h' => kapNew_eq S ⟨h, h'⟩, fun i p v l hv hp he => ?_, fun i t p hp => ?_, fun i p v hv hp => ?_, h4⟩
  · exact h1 i p v l hv ((RealDat3.partAt_updS _ _ _ _ _).1 hp) ((RealDat3.sim_updS _ _ _ _ _ _).1 he)
  · rw [RealDat3.zs_updS]
    exact h2 i t p hp
  · rw [RealDat3.zs_updS]
    exact h3 i p v hv fun hl => hp ((RealDat3.partAt_updS _ _ _ _ _).2 hl)

variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 4000000 in

theorem pins_scal (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) (k l) (hs : ((dat3 f μ R mu tw).updS k l).IsScal (bare3 _ P0 ψ0 P1 ψ1)) :
    Pins ((dat3 f μ R mu tw).updS k l) (bare3 _ P0 ψ0 P1 ψ1) cG := by
  have i := isInert mu tw h.char.inert
  have u := isTup hf h.char.tup n
  have kv := keep mu tw h.keep
  exact ⟨⟨baseW_scal (baseW (A := A3.A) mu tw hf h.char.base e) k _, ⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩,
      fun t => h.char.fullY (f t), fun t => h.char.fullX (f t), fun i t => h.char.fullP i (f t), hs,
      ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, h.char.phase, h.char.allPl⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩, h.phs, h.trSem⟩

set_option maxHeartbeats 4000000 in

theorem pins_kapNew (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) :
    Pins ((dat3 f μ R mu tw).updS (kapNew (dat3 f μ R mu tw)) (dat3 f μ R mu tw).lam3) (bare3 _ P0 ψ0 P1 ψ1) cG :=
  pins_scal hf h e n _ _ (isScal_kapNew _ _ (fun i t => h.char.scal.lam0 i (f t)) h.char.scal.off
    (fun i t => h.char.scal.abs0 i (f t)) h.char.scal.abs fun i t => h.char.scal.tup i (f t))

end Generic

end Res

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

set_option maxHeartbeats 2000000 in

def resRE (h : Wt' ⊆ Wt) : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt') z.Xg z.tr) z.core.Q.c.F :=
  (z.resR h).updS (Res.kapNew (z.resR h)) (z.resR h).lam3

set_option maxHeartbeats 4000000 in

theorem pins_resRE (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) :
    Pins (z.resRE h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  unfold resRE
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact Res.pins_kapNew (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc)

set_option maxHeartbeats 4000000 in

theorem exAt_resR (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resR h).toRealDat.ExAt :=
  Res.exAt (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') e

set_option maxHeartbeats 4000000 in

theorem exAt_resRE (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resRE h).toRealDat.ExAt := Res.exAt_scal (z.exAt_resR h e) _ _

set_option maxHeartbeats 4000000 in

def resGeoE (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resRE h).toRealDat fun _ => 1 :=
  Res.geoScal (z.resGeo h) (Res.kapNew (z.resR h)) (z.resR h).lam (z.resR h).err0

set_option maxHeartbeats 4000000 in

theorem thmB_resR (h : Wt' ⊆ Wt) (hB : z.R.PThmB) : (z.resR h).PThmB :=
  Res.pThmB (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (z.resMu h) (z.resTw Wt') hB

set_option maxHeartbeats 4000000 in

theorem resRE_of_thmB (h : Wt' ⊆ Wt) (hB : z.R.PThmB) : z.resRE h = z.resR h :=
  (congrArg (fun k => (z.resR h).updS k (z.resR h).lam3) (Res.kapNew_of_thmB (z.resR h) (z.thmB_resR h hB))).trans rfl

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

set_option maxHeartbeats 2000000 in

def restrict (hH : Holds z.R z.F) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resR h
  cG := z.cG
  geo := z.resGeo h
  pins := z.pins_resR h hc hH.aux.ex hH.prim.thmB
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le



theorem restrictRealData_constant_error (h : Wt' ⊆ Wt) : (z.resR h).kap = z.R.kap ∧ (z.resR h).err0 = z.R.err0 := ⟨rfl, rfl⟩

set_option maxHeartbeats 1000000 in

theorem restrictRealData_lift_scalar (h : Wt' ⊆ Wt) (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.resR h).lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := rfl


theorem restrict_holds (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Holds (z.restrict hH Wt' h hc).R (z.restrict hH Wt' h hc).F := z.holds_resR h hH

set_option maxHeartbeats 2000000 in

theorem inGeo_resGeo_iff (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.InGeo (z.resGeo h) ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  Res.inGeo_iff (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') (g := z.geo)


variable (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)

theorem mem_nonzero_index_places_iff_at_place_or_conjugate (w : X.B.places.Pl) :
    w ∈ z.W1 F0 ↔ ∃ j, NzAt z.R z.F F0 j (plB X w) ∨ NzAt z.R z.F F0 j (Formalism.DivisionValues.conjPl (plB X w)) := by
  refine exists_congr fun j => ⟨?_, ?_⟩
  · rintro ⟨w', rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem nonzero_index_places_conj_stable : ConjStable X (z.W1 F0) := by
  intro w hw
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate] at hw ⊢
  rw [plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  exact hw.imp fun _ h => h.symm

set_option maxHeartbeats 2000000 in

theorem nzAt_resR (h : Wt' ⊆ Wt) (j : Fin X.toD7.R.m) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    NzAt (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔ NzAt z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) F0 j v := by
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels, columnChoiceReferenceFace_eq_bareFaceTwoLevels]
  exact nzAt_res (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') (lev0 I) (chr0 I) (lev1 I) (chr1 I) F0 j v


theorem complex_side_places_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (N : IndefNum (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.base3) (hN : N.F0 = F0)
    (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr N (X.toD7.plEq w) ↔ w ∈ z.W1 F0 := by
  subst hN
  exact (complexSide_nonzeroIndexPlaces_iff z.R z.F kap lam err Dc Sp Zsc N (plB X w)).trans (z.mem_nonzero_index_places_iff_at_place_or_conjugate N.F0 w).symm

theorem complex_side_face_numbers_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0) (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
      (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) (X.toD7.plEq w) ↔ w ∈ z.W1 F0 :=
  z.complex_side_places_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc _ ((complexSide_numberContents_eq_scaleAtSubspaces z.R z.F kap lam err Dc Sp Zsc C CH).trans hZ) w

theorem twisted_places_eq_complex_side_of_eq_nonzero_index (hW : z.W1 F0 = Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0)
    (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ ((z.R.updS kap lam).withErr err).twPl ↔
      (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
        (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) v := by
  obtain ⟨w, rfl⟩ := (plB X).surjective v
  exact (z.plB_mem_twPl w).trans ((Set.ext_iff.1 hW w).symm.trans (z.complex_side_face_numbers_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc C CH hZ w).symm)

def restrictNonzero (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) := z.restrict hH (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)






set_option maxHeartbeats 4000000 in

def restrictE (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resRE h
  cG := z.cG
  geo := z.resGeoE h
  pins := z.pins_resRE h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

section Ex

variable (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')



set_option maxHeartbeats 2000000 in

theorem restrictOfExists_lift_scalar (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.restrictE e Wt' h hc).R.lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := z.restrictRealData_lift_scalar h i t

set_option maxHeartbeats 2000000 in

theorem restrictOfExists_error_tuples_twisted : (z.restrictE e Wt' h hc).R.err0 = z.R.err0 ∧ (z.restrictE e Wt' h hc).R.mu = z.resMu h ∧
    (z.restrictE e Wt' h hc).R.twPl = z.resTw Wt' := ⟨rfl, rfl, rfl⟩

theorem restrictE_R_of_thmB (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R = z.resR h := z.resRE_of_thmB h hB

set_option maxHeartbeats 2000000 in

theorem restrictE_kap (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R.kap = z.R.kap :=
  (Res.kapNew_of_thmB (z.resR h) (z.thmB_resR h hB)).trans (z.restrictRealData_constant_error h).1



set_option maxHeartbeats 4000000 in

theorem restrictE_holds (hH : Holds z.R z.F) : Holds (z.restrictE e Wt' h hc).R (z.restrictE e Wt' h hc).F := by
  rw [z.restrictE_R_of_thmB e h hc hH.prim.thmB]
  exact z.holds_resR h hH

set_option maxHeartbeats 4000000 in

theorem restrictE_inGeo_iff : GlobalTheory.RealGeo.InGeo (z.restrictE e Wt' h hc).geo ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  (Res.inGeo_geoScal_iff (z.resGeo h) (Res.kapNew (z.resR h)) (z.resR h).lam (z.resR h).err0).trans (z.inGeo_resGeo_iff h)

set_option maxHeartbeats 4000000 in

theorem restrictOfExists_nonzero_places : (z.restrictE e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate, mem_nonzero_index_places_iff_at_place_or_conjugate]
  have key : ∀ j v, NzAt ((z.resR h).updS (Res.kapNew (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔
      NzAt z.R z.F F0 j v := fun j v => (Res.nzAt_scal _ _ _ _ F0 j v).trans (z.nzAt_resR F0 h j v)
  exact exists_congr fun j => or_congr (key j _) (key j _)

end Ex


def restrictNonzeroOfExists (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) :=
  z.restrictE e (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)

section ExW

variable (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt)








end ExW

example (e : z.R.toRealDat.ExAt) : (z.restrictE e ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : Res.kapNew z.R = z.R.kap := Res.kapNew_of_scal z.R z.pins.char.scal.kap

example (hH : Holds z.R z.F) : (z.restrict hH ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : z.resTw Wt = z.R.twPl := Finset.ext fun v => (z.mem_resTw subset_rfl v).trans (z.mem_twPl v).symm

include z in

theorem conjStable : ConjStable X Wt := by
  intro w hw
  have ht := z.pins.char.tup
  rw [← z.plB_mem_twPl, plB_conj]
  by_contra hn
  exact ht.mu_ne _ ((z.plB_mem_twPl w).2 hw) ((ht.mu_conj _).symm.trans (ht.mu_off _ hn))

example (w : X.B.places.Pl) (j : Fin X.toD7.R.m) (h : F0 (plB X w) j ≠ 0) : w ∈ z.W1 F0 :=
  (z.mem_nonzero_index_places_iff_at_place_or_conjugate F0 w).2 ⟨j, Or.inl (Or.inr (Or.inr h))⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

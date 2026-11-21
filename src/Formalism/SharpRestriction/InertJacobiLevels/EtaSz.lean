import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.TiesView
import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e4 : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by rw [two_mul, Real.rpow_add hx]
  have hp : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx.le _
  unfold bTopOf
  rw [e4]
  have h1 : L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ L.sc.eps * L.LaG := mul_le_mul_of_nonneg_left h hp
  have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤
      2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hb
    rw [mul_assoc (2 * (D.R.n : ℝ) * L.sc.delta1) (L.sc.x ^ L.sc.eps) L.LaG]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

def mkSc (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (x : ℝ) (hx : 1 < x) : Scale := ⟨x, eps, hx, h0, h1, 1, le_rfl⟩

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem FC.Large.mono {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large K' CH) (hK : K.le K') : C.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

def fcOf (p t : ℝ) (o : Out) (M N : ℝ) : FC where
  Ct := t
  Cc := o.Cc
  CT2 := o.CT2
  CGam := M
  Csz := M
  Cr := 1
  CTu := o.CTu
  Cdg := o.Cdg
  C5 := o.C5
  full := o.full
  GK := ⟨M, N, N, N, N, N, N, N, N, N, N, 5, 4, 1, N⟩
  cX := ⟨1, ⟨12, 3, M⟩⟩
  P := ⟨N, N, N, N⁻¹, 10, N, N, o.CLw, o.Cj0, N, o.cw, N, N, N, N, N, N, o.CetaF, N, o.CYL, o.Cpde, o.CccK, M⟩
  T := ⟨p, o.eP, o.Cp, N, o.cTO, N, N⟩

theorem exists_large (K : TransportedAlt) (out : ℝ → ℝ → Out) :
    ∃ (C : FC) (CH : ℝ), 0 ≤ CH ∧ C.out = out C.T.CP C.Ct ∧ C.GK.Nonneg ∧ 1 ≤ C.Cr ∧ C.Large K CH ∧ C.P.CF = CH ∧
      C.GK.Pr1 = 1 ∧ C.GK.dl1 = 5 ∧ C.GK.dl2 = 4 ∧ C.cX.Ce = 1 ∧ C.cX.err.c6 = 12 ∧ C.cX.err.dig = 3 ∧ C.Cr = 1 ∧
      C.P.CnW = 10 ∧ C.Ct = 401 := by
  set p := K.pre with hp
  set t : ℝ := 401 with ht
  set o := out p t with ho
  set M := max (K.mid (fcOf p t o 0 0).cOut) 1 with hM
  set N := max (K.last ((fcOf p t o 0 0).cOut ++ (fcOf p t o M 0).cMid M)) 1 with hN
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hN0 : 0 ≤ N := le_trans zero_le_one (le_max_right _ _)
  refine ⟨fcOf p t o M N, M, hM0, rfl, ⟨hM0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, by show (0 : ℝ) ≤ 5; norm_num, by show (0 : ℝ) ≤ 4; norm_num,
      by show (0 : ℝ) ≤ 1; norm_num, hN0⟩,
    le_refl _, ⟨?_, trivial, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    have hc' : c = p := by
      simp only [FC.cPre, fcOf, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact hc
    rw [hc']
  · intro c hc
    have hc' : c = M := by
      simp only [FC.cMid, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _
  · intro c hc
    have hc' : c = N := by
      simp only [FC.cLast, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self, inv_inv] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

abbrev KapI : Type := ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ


structure LatIn (D : D7) where
  Vram : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn
  len : D.what₂.Word → D.what₂.places.Pl → ℚ

def LatIn.zero (D : D7) : LatIn D := ⟨fun _ _ _ => ⊥, fun _ _ => 0⟩

structure TieHyp {D : D7} (gatT : GatTies D) (L0 : SizeData₂ D) (kapI : KapI) (ep : ℕ → ℕ) where

  hw : 1 ≤ L0.sc.w'' D.R.n

  hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i))

  hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0

  htw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L0.sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ L0.supp

  pos : PosHyp gatT (instW L0 kapI ep)

  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L0
  hcl : L0.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c

  hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
    |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c

  hw1 : ∀ τ, (c : ℝ) ≤ wj D 1 τ - G.kaJ D 1

namespace TieHyp

variable {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ} (H : TieHyp gatT L0 kapI ep)
  (K : G.Consts) (Cr : ℝ) (Λ : LatIn D)

def L : SizeData₂ D := tieL L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def Gx : G.Inst D (H.L K Cr Λ) := tieX L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu

def posL : PosHyp gatT (H.Gx K Cr Λ) where
  vOf := H.pos.vOf
  inj := H.pos.inj
  n_eq := H.pos.n_eq
  pos := H.pos.pos
  r_eq := H.pos.r_eq

def latHyp : LatHyp gatT (H.Gx K Cr Λ) := latHypOf gatT (H.Gx K Cr Λ) (H.posL K Cr Λ) H.c H.c_le H.hcl H.hoff H.hw1

def Gy : G.LatInst D := { (H.latHyp K Cr Λ).latInst with Vram := Λ.Vram }

theorem supp_sat (w : D.what₂.places.Pl) (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (H.L K Cr Λ).sc.X'' D.R.n) :
    w ∈ (H.L K Cr Λ).supp :=
  tieL_supp_sat L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu w h

theorem tw_supp (w : D.what₂.places.Pl) (h : D.what₂.muAt w ≠ D.what₂.mu0) : w ∈ (H.L K Cr Λ).supp :=
  (mem_tieSupp L0 w).2 (H.htw w h)

theorem fills (w : D.what₂.places.Pl) : G.ParametersFill (H.Gx K Cr Λ) K w :=
  tieL_fills L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu (instW_fill L0 kapI ep) w



theorem latTied : G.LatTied gatT (H.Gx K Cr Λ) (H.Gy K Cr Λ) := (H.latHyp K Cr Λ).latTied (instW_fill L0 kapI ep)

theorem drop_iff (p : ℕ) :
    p ∈ (H.L K Cr Λ).drop ↔ NoGain (H.Gx K Cr Λ) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  tieL_drop_iff L0 (instW L0 kapI ep) K Cr Λ.len H.hw H.hg H.hu p



end TieHyp


open Classical in

def offShd (R : Ranks) (TTn : Finset ℕ) (sc : Scale) (offS : ℕ → ℕ → ℝ) (j t : ℕ) : ℝ :=
  if j ∈ Finset.Icc 1 R.m then offS j (t % R.n)
  else if t % R.n ∈ TTn then sc.b' / sc.x else sc.w'' R.n





end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def TieHyp.tiesAtY {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D) (Gy : G.LatInst D)
    (hGy : G.LatTied gatT (H.Gx C.GK C.Cr Λ) Gy)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) Gy C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := Gy
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := hGy
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

def TieHyp.tiesAt {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) (H.Gy C.GK C.Cr Λ) C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := H.Gy C.GK C.Cr Λ
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := H.latTied C.GK C.Cr Λ
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure Shd0 where
  R : Ranks
  TTn : Finset ℕ
  T2 : Finset ℕ
  q : ℕ
  d : ℕ
  g : Fin 2 → ℕ
  pde : ℕ
  pde' : ℕ
  bits : ℕ → Bool
  etaSz : ℝ
  Sc : ℝ
  hP : ℕ → ℕ
  offS : ℕ → ℕ → ℝ
  kapI : KapI
  ep : ℕ → ℕ

def Shd0.shd (S : Shd0) (sc : Scale) (C : FC) : Shd where
  R := S.R
  TTn := S.TTn
  T2 := S.T2
  q := S.q
  d := S.d
  g := S.g
  pde := S.pde
  pde' := S.pde'
  bits := S.bits
  LaG := G.La C.GK sc
  etaSz := S.etaSz
  Sc := S.Sc
  hP := S.hP
  bs := fun h t => bsVal (2 ^ S.R.e) (h % 2 ^ S.R.e) (t % 2 ^ S.R.e)
  off := offShd S.R S.TTn sc S.offS
  kapI := S.kapI
  ep := S.ep

end Formalism.MainNotions.Inhab

end
end

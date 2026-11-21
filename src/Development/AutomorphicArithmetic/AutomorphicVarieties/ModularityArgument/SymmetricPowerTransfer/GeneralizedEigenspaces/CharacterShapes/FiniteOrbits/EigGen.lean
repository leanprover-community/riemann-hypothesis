import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.ValInvGe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open GlobalTheory.SplitWeil
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem finOrb_subgroupOf {G : Type} [Group G] (H J : Subgroup G) (d : H) (h : AlgebraTools.FinOrb J J (d : G)) :
    AlgebraTools.FinOrb (J.subgroupOf H) (J.subgroupOf H) d := by
  let f : H ⧸ J.subgroupOf H → G ⧸ J := Quotient.map' (fun x : H => (x : G)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Subgroup.mem_subgroupOf.1 hab)
  have hf : Function.Injective f := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    intro hab
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (QuotientGroup.eq.1 hab))
  refine Set.Finite.of_finite_image (Set.Finite.subset h ?_) hf.injOn
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨⟨u.1.1, Subgroup.mem_subgroupOf.1 u.2⟩, rfl⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem det_cLoc (x : UA L 2) (u : Plc L) :
    (mL u x).det = pLoc L u (pFin L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det) := by
  have h : mL u x = ((pLoc L u).comp (pFin L)).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) := rfl
  rw [h, ← RingHom.map_det]
  rfl

private theorem det_places (x : UA L 2) (hx : x ∈ SUA L) (u : Plc L) : (mL u x).det = 1 := by
  have h : ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 :=
    congrArg Units.val (show Matrix.GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1 from hx)
  rw [det_cLoc, h, map_one, map_one]

private theorem mem_SUA_of_places (x : UA L 2) (hx : x ∈ finU L 2) (h : ∀ u : Plc L, (mL u x).det = 1) : x ∈ SUA L := by
  show Matrix.GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1
  apply Units.ext
  show ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1
  have hi : (pInf L).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) = 1 :=
    congrArg (fun y : GL (Fin 2) (Cinf L) => (y : Matrix (Fin 2) (Fin 2) (Cinf L))) (show cInf x = 1 from hx)
  apply Prod.ext
  · refine (infEq L).symm.injective ?_
    have := RingHom.map_det (pInf L) ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L))
    rw [hi, Matrix.det_one] at this
    exact this.trans (map_one (pInf L)).symm
  · apply Subtype.ext
    funext u
    have := det_cLoc x u
    rw [h u] at this
    exact this.symm.trans rfl

private theorem dc_eq_of_local {G M Gl V : Type} [Group G] [Group M] [Group Gl] [AddCommGroup V] [Module ℂ V]
    (Q : Subgroup M) (e : G ≃* Q) (sec : Gl →* M) (c : M →* Gl) (hcs : ∀ x, c (sec x) = x)
    (hsu : ∀ x ∈ Q, sec (c x) ∈ Q)
    (hcomm : ∀ x ∈ Q, ∀ h, sec h ∈ Q → Commute (sec h) (x * (sec (c x))⁻¹))
    (J₀ : Subgroup Gl) (U₁ U₂ : Subgroup G)
    (h₁ : ∀ u ∈ U₁, c (e u) ∈ J₀) (h₂ : ∀ u ∈ U₂, c (e u) ∈ J₀)
    (h₃ : ∀ u : G, (∃ h ∈ J₀, (e u : M) = sec h) → u ∈ U₁) (h₁₂ : U₁ ≤ U₂)
    (d : Gl) (hd : AlgebraTools.FinOrb J₀ J₀ d) (g : G) (hg : (e g : M) = sec d)
    (ψ : G → V) (hψ : ∀ u ∈ U₂, ∀ x, ψ (x * u) = ψ x) : dcF U₁ g ψ = dcF U₂ g ψ := by
  let Hs : Subgroup Gl := Q.comap sec
  let j : Hs →* G := e.symm.toMonoidHom.comp (sec.subgroupComap Q)
  let p : G →* Hs := MonoidHom.codRestrict (c.comp (Q.subtype.comp e.toMonoidHom)) Hs (fun u => hsu _ (e u).2)
  have hej : ∀ x : Hs, (e (j x) : M) = sec x := fun x => by
    show ((e (e.symm _)) : M) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hp : ∀ u : G, (p u : Gl) = c (e u) := fun _ => rfl
  let J : Subgroup Hs := J₀.subgroupOf Hs
  have hpj : ∀ x, p (j x) = x := fun x => Subtype.ext (by rw [hp, hej, hcs])
  have hcm : ∀ (u : G) (x : Hs), u * (j (p u))⁻¹ * j x = j x * (u * (j (p u))⁻¹) := by
    intro u x
    apply e.injective
    apply Subtype.ext
    have := hcomm _ (e u).2 x x.2
    simp only [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, hej, hp]
    exact this.symm.eq
  have hJ₁ : ∀ h ∈ J, j h ∈ U₁ := fun h hh => h₃ _ ⟨h, Subgroup.mem_subgroupOf.1 hh, hej h⟩
  have hdH : d ∈ Hs := by
    show sec d ∈ Q
    rw [← hg]
    exact (e g).2
  have hgj : g = j ⟨d, hdH⟩ := by
    apply e.injective
    apply Subtype.ext
    rw [hg, hej]
  have hfin : AlgebraTools.FinOrb J J (⟨d, hdH⟩ : Hs) := finOrb_subgroupOf Hs J₀ _ hd
  have k₁ := dcLocal Hs G V j p J U₁ hpj
    (fun u hu => ⟨Subgroup.mem_subgroupOf.2 (h₁ u hu), hcm u⟩) hJ₁ _ hfin
  have k₂ := dcLocal Hs G V j p J U₂ hpj
    (fun u hu => ⟨Subgroup.mem_subgroupOf.2 (h₂ u hu), hcm u⟩) (fun h hh => h₁₂ (hJ₁ h hh)) _ hfin
  rw [hgj, k₁.2 ψ fun u hu => hψ u (h₁₂ hu), k₂.2 ψ hψ]

private theorem sec_cLoc (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU L 2) (u : Plc L) (hu : un u = un w) :
    cLoc u (secW 2 w (cLoc w x)) = cLoc u x := by
  obtain ⟨f1, -, -, -, -, -, f7, -⟩ := uaFacts L 2
  obtain ⟨a, ha, hau⟩ := f7 w x hx
  have e : a = secW 2 w (cLoc w x) := by
    have := (f1 w h).2.2.2 a ha
    rwa [hau w rfl] at this
  rw [← e]
  exact hau u hu

private theorem loc_off (w : Plc L) (x : UA L 2) (hx : x ∈ locU 2 w) (u : Plc L) (hu : un u ≠ un w) : cLoc u x = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu

private theorem sec_mem (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU L 2 ⊓ SUA L) :
    secW 2 w (cLoc w x) ∈ finU L 2 ⊓ SUA L := by
  have hl : secW 2 w (cLoc w x) ∈ locU 2 w := ((uaFacts L 2).1 w h).1 _
  have hf : secW 2 w (cLoc w x) ∈ finU L 2 := (Subgroup.mem_inf.1 hl).1
  refine Subgroup.mem_inf.2 ⟨hf, mem_SUA_of_places _ hf fun u => ?_⟩
  by_cases hu : un u = un w
  · have := det_places x (Subgroup.mem_inf.1 hx).2 u
    rwa [mL, ← sec_cLoc w h x (Subgroup.mem_inf.1 hx).1 u hu] at this
  · rw [mL, loc_off w _ hl u hu]
    simp

private theorem sec_comm (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU L 2) (a : GL (Fin 2) (Kw w)) :
    Commute (secW 2 w a) (x * (secW 2 w (cLoc w x))⁻¹) := by
  refine (uaFacts L 2).2.1 w _ (((uaFacts L 2).1 w h).1 a) _ fun u hu => ?_
  rw [map_mul, map_inv, sec_cLoc w h x hx u hu, mul_inv_cancel]

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (a : s * s = Δ) (b : s' * s' = Δ) (h : s = s') : eD a = eD b := by
  subst h; rfl

private theorem iw_KGL (R : RingBr L) (w : Plc L) (Sp : R.Split w) (a : GL (Fin 2) (Kw w)) (ha : a ∈ (iw w).J 2) :
    a ∈ GlobalTheory.LFun.KGL w 2 := by
  let g₀ : GL (Fin 2) (Kv (un w)) := Matrix.GeneralLinearGroup.map (Sp.i.symm : Kw w →+* Kv (un w)) a
  have e : Matrix.GeneralLinearGroup.map (Sp.i : Kv (un w) →+* Kw w) g₀ = a := by
    ext i j
    simp [g₀]
  rw [← e] at ha ⊢
  exact (Sp.K 2 g₀).2 (((finFacts _ (Lev.iw _)).2.2.2.2.2 2).2.2.2 ((Sp.J (Lev.iw _) (iw w) rfl Sp.Uo 2 g₀).1 ha))

private theorem sec_lev (R : RingBr L) (w : Plc L) (h : IsSplitAt w) (Sp : R.Split w) (U : Subgroup (UA L 2)) (hU : Full U {w})
    (S₁ : Finset (Plc L)) (hS : ∀ w' ∈ S₁, w' ≠ w → un w' ≠ un w) (a : GL (Fin 2) (Kw w)) (ha : a ∈ (iw w).J 2) :
    secW 2 w a ∈ lev U S₁ iw := by
  have hl : secW 2 w a ∈ locU 2 w := ((uaFacts L 2).1 w h).1 a
  have hc : cLoc w (secW 2 w a) = a := ((uaFacts L 2).1 w h).2.1 a
  have hK : secW 2 w a ∈ Kall L 2 := by
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hl).1, Subgroup.mem_iInf.2 fun u => ?_⟩
    show cLoc u (secW 2 w a) ∈ GlobalTheory.LFun.KGL u 2
    by_cases hu : un u = un w
    · exact (uaFacts L 2).2.2.2.2.2.2.2 w h _ (by rw [hc]; exact iw_KGL R w Sp a ha) u hu
    · rw [loc_off w _ hl u hu]
      exact one_mem _
  refine Subgroup.mem_inf.2 ⟨hU.2 w (Finset.mem_singleton_self w) (Subgroup.mem_inf.2 ⟨hl, hK⟩), ?_⟩
  refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
  show cLoc w' (secW 2 w a) ∈ (iw w').J 2
  by_cases e : w' = w
  · subst e
    rwa [hc]
  · rw [loc_off w _ hl w' (hS w' hw' e)]
    exact one_mem _

private theorem lvS_loc (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok)
    (hF : Fit T S VL A) (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hiw : VL w = iw w) (y : DA B.Δ) (hy : A.dat.Off y)
    (u : SA B.Δ) (hu : u ∈ A.lvS y) : cLoc w (B.bS u : UA L 2) ∈ (iw w).J 2 := by
  have hv : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
  have h1 : y⁻¹ * (u : DA B.Δ) * y⁻¹⁻¹ ∈ A.dat.U2 := Subgroup.mem_subgroupOf.1 hu
  have h2 := (((datOk _ _ A hA).2.2.2.2 _).1 h1).1 (un w) hv
  have h3 : (y⁻¹ * (u : DA B.Δ) * y⁻¹⁻¹).1 (un w) = (u : DA B.Δ).1 (un w) := by
    show (y.1 (un w))⁻¹ * (u : DA B.Δ).1 (un w) * ((y.1 (un w))⁻¹)⁻¹ = _
    rw [hy _ hv]
    simp
  rw [h3, eD_congr (A.hs _ hv) (T w h).hs (hF.s w hw h)] at h2
  rw [hB.splS w (T w h) u, ← hiw]
  exact ((T w h).J (A.V (un w)) (VL w) (hF.c w hw) (hF.H w hw h) 2 _).2 h2

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

private theorem genL {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) (y : DA Δ) {M Gl V : Type} [Group M] [Group Gl] [AddCommGroup V] [Module ℂ V]
    (Q : Subgroup M) (e : SA Δ ≃* Q) (sec : Gl →* M) (c : M →* Gl) (hcs : ∀ x, c (sec x) = x)
    (hsu : ∀ x ∈ Q, sec (c x) ∈ Q) (hcomm : ∀ x ∈ Q, ∀ h, sec h ∈ Q → Commute (sec h) (x * (sec (c x))⁻¹))
    (J₀ : Subgroup Gl) (U : Subgroup M) (h₁ : ∀ u ∈ U, c u ∈ J₀) (h₂ : ∀ u : SA Δ, u ∈ A.lvS y → c (e u) ∈ J₀)
    (h₃ : ∀ h ∈ J₀, sec h ∈ U) (h₁₂ : ∀ u : SA Δ, (e u : M) ∈ U → u ∈ A.lvS y)
    (d : Gl) (hd : AlgebraTools.FinOrb J₀ J₀ d) (g : SA Δ) (hg : (e g : M) = sec d)
    (ψ : SA Δ → V) (hψ : ∀ u ∈ A.lvS y, ∀ x, ψ (x * u) = ψ x) :
    dcF ((U.subgroupOf Q).comap e.toMonoidHom) g ψ = dcF (A.lvS y) g ψ :=
  dc_eq_of_local Q e sec c hcs hsu hcomm J₀ _ _ (fun _ hu => h₁ _ hu) h₂
    (fun u hu => hu.elim fun h hh => show (e u : M) ∈ U from hh.2 ▸ h₃ h hh.1) (fun u hu => h₁₂ u hu) d hd g hg ψ hψ

private theorem sLev0 {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (w : Plc L) (hwS : w ∈ S) (h : IsSplitAt w)
    (S₁ : Finset (Plc L)) (hwS₁ : w ∈ S₁) (hS₁ : S₁ ⊆ S) (hiw : VL w = iw w) (U : Subgroup (UA L 2)) (hU : Full U {w})
    (y : DA B.Δ) (hy : A.dat.Off y) (hlev : ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ lev U S₁ iw → g ∈ A.lvS y)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ψ : SA B.Δ → V) (hψ : ∀ u ∈ A.lvS y, ∀ g, ψ (g * u) = ψ g) (g : SA B.Δ)
    (d : Fin 2 → (Kw w)ˣ) (hg : (B.bS g : UA L 2) = secW 2 w (Sig.dg d)) :
    dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap B.bS.toMonoidHom) g ψ = dcF (A.lvS y) g ψ :=
  genL A y (finU L 2 ⊓ SUA L) B.bS (secW 2 w) (cLoc w) ((uaFacts L 2).1 w h).2.1 (sec_mem w h)
    (fun x hx a _ => sec_comm w h x hx.1 a) ((iw w).J 2) (lev U S₁ iw)
    (fun _ hu => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 w) hwS₁)
    (lvS_loc B hB T S VL A hA hF w hwS h hiw y hy)
    (sec_lev B.toRingBr w h (T w h) U hU S₁ fun _ hw' e e' => e (hF.pl.inj (Finset.mem_coe.2 (hS₁ hw')) (Finset.mem_coe.2 hwS) e'))
    hlev (Sig.dg d) (((finFacts _ (iw w)).2.2.2.2.2 2).1 _) g hg ψ hψ

end UpperTheory.V.Z.Sym.So

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq dcF SD.lvS lev SUA Subgroup.comap MulEquiv.toMonoidHom Subgroup.toGroup Subgroup.subgroupOf

theorem UpperTheory.V.Z.Sym.So.sLev :
    UpperTheory.V.Z.Sym.So.SLev := by
  intro L _ _ _ B hB T S VL A hA hF w hw h S₁ a b c U hU y hy hl V _ _ ψ hψ g d hg
  have k := sLev0 B hB T S VL A hA hF w hw h S₁ a b c U hU y hy hl V ψ hψ g d hg
  exact k

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.OS

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private def eG {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) : H ≃* ↥((SUA L).subgroupOf (finU L 2)) := E.trans eT

private def psi {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {V : Type} (ψ : H → V) (s : ↥((SUA L).subgroupOf (finU L 2))) : V := ψ ((eG E).symm s)

private theorem psi_e {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {V : Type} (ψ : H → V) (g : H) : psi E ψ (eG E g) = ψ g := by
  show ψ ((eG E).symm (eG E g)) = _
  rw [MulEquiv.symm_apply_apply]

private instance : (finU L 2).Normal := by unfold finU; infer_instance

private theorem out_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) (p : UA L 2 →* finU L 2)
    (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f)
    (hp2 : ∀ x : UA L 2, ∃ k ∈ infU L 2, x = (p x : UA L 2) * k)
    {m : ℕ} (hm : 3 ≤ m) {U : Subgroup (UA L 2)} (hU : IsCong m U) (U₁ : Subgroup (UA L 2)) (hU₁ : U₁ ≤ U) (hfin : U₁ ≤ finU L 2)
    {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n)
    (hleft : ∀ (γ : ratU L 2) (g g' : ↥((SUA L).subgroupOf (finU L 2))), (g' : finU L 2) = p γ.1 * g →
      psi E ψ g' = repE n (0 : InfinitePlace L → ℤ) (infC L 2 γ.1) (psi E ψ g))
    (hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ U₁.subgroupOf (finU L 2) → ∀ g, psi E ψ (g * u) = psi E ψ g) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) n, IsAF (repE n (0 : InfinitePlace L → ℤ)) U₁ φ ∧ (∀ g : H, φ (E g : UA L 2) = ψ g) ∧
      ∀ (a : ↥((SUA L).subgroupOf (finU L 2))) (c : ℂ), AlgebraTools.FinOrb U₁ U₁ ((a : finU L 2) : UA L 2) →
        AlgebraTools.FinOrb (U₁.subgroupOf (finU L 2)) (U₁.subgroupOf (finU L 2)) (a : finU L 2) →
        (∀ u ∈ U₁.subgroupOf (finU L 2), ∃ z ∈ U₁.subgroupOf (finU L 2), z * (a : finU L 2) = a * z ∧
          u * z⁻¹ ∈ (SUA L).subgroupOf (finU L 2) ∧ z⁻¹ * u ∈ (SUA L).subgroupOf (finU L 2)) →
        dcF ((U₁.subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) a (psi E ψ) = c • psi E ψ →
        dcF U₁ ((a : finU L 2) : UA L 2) φ = c • φ := by
  have hroot : ∀ γ : ratU L 2, ∀ u ∈ U₁.subgroupOf (finU L 2),
      (p.comp (ratU L 2).subtype) γ * u ∈ (SUA L).subgroupOf (finU L 2) → (p.comp (ratU L 2).subtype) γ ∈ (SUA L).subgroupOf (finU L 2) := by
    intro γ u hu h
    obtain ⟨k, hk, hγ⟩ := hp2 γ.1
    have hr : (p γ.1 : UA L 2) * k ∈ ratU L 2 := by rw [← hγ]; exact γ.2
    exact Subgroup.mem_subgroupOf.2 (detRoot L m hm U hU _ (p γ.1).2 k hk hr u
      (hU₁ (Subgroup.mem_subgroupOf.1 hu)) (Subgroup.mem_subgroupOf.1 h)).1
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := extF (ratU L 2) (finU L 2) (Wt.VD (InfinitePlace L) n) (p.comp (ratU L 2).subtype)
    ((repE n (0 : InfinitePlace L → ℤ)).comp ((infC L 2).comp (ratU L 2).subtype))
    ((SUA L).subgroupOf (finU L 2)) (U₁.subgroupOf (finU L 2)) comm_mem hroot (psi E ψ) hleft hright
  obtain ⟨φ, hAF, hφ2, hφ3⟩ := finToAF L 2 (Wt.VD (InfinitePlace L) n) (repE n (0 : InfinitePlace L → ℤ)) U₁ hfin Φ
    (by
      intro f k hk hr g
      have h₁ := hΦ2 ⟨_, hr⟩ g
      have e₁ : (p.comp (ratU L 2).subtype) ⟨_, hr⟩ = f := hp1 f k hk
      rw [e₁] at h₁
      rw [h₁]
      show repE n (0 : InfinitePlace L → ℤ) (infC L 2 ((f : UA L 2) * k)) _ = _
      rw [map_mul, infC_fin f.2, one_mul])
    (fun u hu g => hΦ3 u (Subgroup.mem_subgroupOf.2 hu) g)
  refine ⟨φ, hAF, fun g => ?_, fun a c h₁ h₂ h₃ h₄ => hφ3 a c h₁ (hΦ4 a c h₂ h₃ h₄)⟩
  exact (hφ2 (eG E g : finU L 2)).trans ((hΦ1 (eG E g)).trans (psi_e E ψ g))

private theorem eig_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {S₁ : Finset (Plc L)} (hpl₁ : Places (S₁ : Set (Plc L)))
    {U : Subgroup (UA L 2)} (hFull : Full U S₁) {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n)
    (hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ ((lev U S₁ iw).subgroupOf (finU L 2)) → ∀ g, psi E ψ (g * u) = psi E ψ g)
    (φ : UA L 2 → Wt.VD (InfinitePlace L) n) (hφi : ∀ u ∈ lev U S₁ iw, ∀ g, φ (g * u) = φ g)
    (hφ : ∀ (a : ↥((SUA L).subgroupOf (finU L 2))) (c : ℂ), AlgebraTools.FinOrb (lev U S₁ iw) (lev U S₁ iw) ((a : finU L 2) : UA L 2) →
        AlgebraTools.FinOrb ((lev U S₁ iw).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (a : finU L 2) →
        (∀ u ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), ∃ z ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), z * (a : finU L 2) = a * z ∧
          u * z⁻¹ ∈ ((SUA L).subgroupOf (finU L 2)) ∧ z⁻¹ * u ∈ ((SUA L).subgroupOf (finU L 2))) →
        dcF (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) a (psi E ψ) = c • psi E ψ →
        dcF (lev U S₁ iw) ((a : finU L 2) : UA L 2) φ = c • φ)
    {w : Plc L} (hw : w ∈ S₁) (d₀ : Fin 2 → (Kw w)ˣ) (c : ℂ) (g : H) (hsec : (E g : UA L 2) = secW 2 w (Sig.dg d₀))
    (hoff : ∀ u, un u ≠ un w → cLoc u (E g : UA L 2) = 1) (d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ)
    (hcl : ∀ w' ∈ S₁, cLoc w' (E g : UA L 2) = Sig.dg (d w'))
    (hE : dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom) g ψ = c • ψ) : EigAt φ w (iw w) d₀ c := by
  have hUfin : lev U S₁ iw ≤ finU L 2 := fun x hx => (hFull.1 hx.1).1
  have hFw : Full U {w} := ⟨hFull.1, fun w' h' => hFull.2 w' (by rw [Finset.mem_singleton.1 h']; exact hw)⟩
  have hdc := dcAt L 2 U S₁ iw hpl₁ w hw hFw d₀
  have hfo := hdc.1
  refine (hdc.2 _ φ hφi _).2 ?_
  rw [← hsec] at hfo ⊢
  have hz : ∀ u ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), ∃ z ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), z * (eG E g : finU L 2) = (eG E g : finU L 2) * z ∧
      u * z⁻¹ ∈ ((SUA L).subgroupOf (finU L 2)) ∧ z⁻¹ * u ∈ ((SUA L).subgroupOf (finU L 2)) := by
    intro u hu
    obtain ⟨c₀, hc₀, h₁, h₂, h₃⟩ := torUA L U S₁ iw hpl₁ hFull u (Subgroup.mem_subgroupOf.1 hu)
    have hcm := h₃ (E g : UA L 2) d ⟨(E g).2.1, fun u' hu' => hoff u' (hu' w hw)⟩ hcl
    exact ⟨⟨c₀, hUfin hc₀⟩, Subgroup.mem_subgroupOf.2 hc₀, Subtype.ext hcm, Subgroup.mem_subgroupOf.2 h₁.2, Subgroup.mem_subgroupOf.2 h₂.2⟩
  have hfo' : AlgebraTools.FinOrb ((lev U S₁ iw).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (eG E g : finU L 2) :=
    (dcSub (UA L 2) ℂ (finU L 2) (lev U S₁ iw) (eG E g : finU L 2) hfo
      (fun u hu => ⟨1, one_mem _, by rw [mul_one, one_mul], by rw [inv_one, mul_one]; exact hUfin hu, by rw [inv_one, one_mul]; exact hUfin hu⟩) inferInstance).1
  have hfo'' := (dcSub (finU L 2) ℂ ((SUA L).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (eG E g) hfo' hz inferInstance).1
  refine hφ (eG E g) _ hfo hfo' hz ?_
  have hmp := (dcMap H ↥((SUA L).subgroupOf (finU L 2)) (Wt.VD (InfinitePlace L) n) (eG E).toMonoidHom (eG E).bijective (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) g g).2.2.2 hfo'' (psi E ψ)
    (fun u hu g' => hright u (Subgroup.mem_subgroupOf.1 hu) g')
  have hψE : psi E ψ ∘ (eG E).toMonoidHom = ψ := funext fun g' => psi_e E ψ g'
  have hcmp : (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))).comap (eG E).toMonoidHom = ((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hψE, hcmp, hE] at hmp
  funext s
  obtain ⟨g', rfl⟩ := (eG E).surjective s
  have h₅ := congrFun hmp g'
  refine h₅.symm.trans ?_
  show c • ψ g' = c • psi E ψ (eG E g')
  rw [psi_e]

private theorem all_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {S₁ : Finset (Plc L)} (hpl₁ : Places (S₁ : Set (Plc L)))
    {m : ℕ} (hm : 3 ≤ m) {U : Subgroup (UA L 2)} (hU : IsCong m U) (hFull : Full U S₁) {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n) (hψ : ψ ≠ 0)
    (p : UA L 2 →* finU L 2) (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f)
    (hp2 : ∀ x : UA L 2, ∃ k ∈ infU L 2, x = (p x : UA L 2) * k)
    (hleft : ∀ (γ : ratU L 2) (g g' : ↥((SUA L).subgroupOf (finU L 2))), (g' : finU L 2) = p γ.1 * g →
      ψ ((E.trans eT).symm g') = repE n (0 : InfinitePlace L → ℤ) (infC L 2 γ.1) (ψ ((E.trans eT).symm g)))
    (hlv : ∀ u : H, (E u : UA L 2) ∈ lev U S₁ iw → ∀ g, ψ (g * u) = ψ g) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ)
    (hel : ∀ w ∈ S₁, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 → ∃ (g : H) (d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ),
      (E g : UA L 2) = secW 2 w (Sig.dg ![t, t⁻¹]) ∧ (∀ u, un u ≠ un w → cLoc u (E g : UA L 2) = 1) ∧
      (∀ w' ∈ S₁, cLoc w' (E g : UA L 2) = Sig.dg (d w')) ∧
      dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom) g ψ = Dict.expo ![a w, 1] ![t, t⁻¹] • ψ) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) n, φ ≠ 0 ∧ IsAF (repE n 0) (lev U S₁ iw) φ ∧ ∀ w ∈ S₁, Dict.EigS φ w (iw w) (a w) := by
  have hUle : lev U S₁ iw ≤ U := fun x hx => hx.1
  have hUfin : lev U S₁ iw ≤ finU L 2 := fun x hx => (hFull.1 hx.1).1
  have hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ ((lev U S₁ iw).subgroupOf (finU L 2)) → ∀ g, psi E ψ (g * u) = psi E ψ g := by
    intro u hu g
    show ψ ((eG E).symm (g * u)) = ψ ((eG E).symm g)
    rw [map_mul]
    refine hlv _ ?_ _
    show (((eG E ((eG E).symm u) : ↥((SUA L).subgroupOf (finU L 2))) : finU L 2) : UA L 2) ∈ lev U S₁ iw
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hu
  obtain ⟨φ, hAF, hval, hφ⟩ := out_gen E p hp1 hp2 hm hU (lev U S₁ iw) hUle hUfin ψ hleft hright
  have hne : φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ
    intro h
    exact hg (by rw [← hval, h]; rfl)
  refine ⟨φ, hne, hAF, fun w hw t ht => ?_⟩
  obtain ⟨g, d, h1, h2, h3, h4⟩ := hel w hw t ht
  exact eig_gen E hpl₁ hFull ψ hright φ hAF.level hφ hw _ _ g h1 h2 d h3 h4

end UpperTheory.V.Z.Sym.So.OS

set_option allowUnsafeReducibility true in
attribute [local irreducible] DX KD RP SA

open UpperTheory.V.Z.Sym.So.OS in
set_option maxHeartbeats 2000000 in
theorem UpperTheory.V.Z.Sym.So.outS :
    UpperTheory.V.Z.Sym.So.OutS := by
  intro L _ _ _ B hB T S VL A hA hF S₁ hS₁ hiw m U hm hU hFull n e a b hab ι hι y hy hlev ψ hψ hSF
  classical
  obtain ⟨p, hp1, hp2⟩ := exFin (L := L) 2
  have hpl₁ : Places (S₁ : Set (Plc L)) :=
    ⟨fun w' hw' => hF.pl.split w' (hS₁ hw'), hF.pl.inj.mono (by exact_mod_cast hS₁)⟩
  have h1 := left_eq B hB p hp1 hp2 hm hU ι hι (e := e) ψ hSF.left
  refine all_gen B.bS hpl₁ hm hU hFull ψ hψ p hp1 hp2 h1 (fun u hu => hSF.level u (hlev u hu)) a fun w hw t ht => ?_
  have hwS := hS₁ hw
  have h := hF.pl.split w hwS
  have hFw : Full U {w} := ⟨hFull.1, fun w' h' => hFull.2 w' (by rw [Finset.mem_singleton.1 h']; exact hw)⟩
  refine (place_el hB T hA hF hab hwS h t ht).elim fun t' H1 => H1.elim fun g H => ?_
  have hsl := sLev L B hB T S VL A hA hF w hwS h S₁ hw hS₁ (hiw w hw) U hFw y hy hlev _ ψ hSF.level g ![t, t⁻¹] H.2.2.2.1
  have he := hSF.eig t' g H.2.1 H.1
  exact ⟨g, fun w' => if h' : IsSplitAt w' then fun i => iu T w' h' (SD.dS t' (un w') i) else 1, H.2.2.2.1, H.2.2.2.2.1,
    fun w' hw' => (H.2.2.2.2.2 w' (hS₁ hw') (hF.pl.split w' (hS₁ hw'))).trans (by beta_reduce; rw [dif_pos (hF.pl.split w' (hS₁ hw'))]),
    hsl.trans (he.trans (congrArg (· • ψ) H.2.2.1))⟩

end
end

module

public import Formalism.LocalToGlobal.Columns.TiedCrd
public import Formalism.LocalToGlobal.Columns.RecLevelStep
public import Formalism.LocalToGlobal.Columns.RecLevelAsm
public import Formalism.LocalToGlobal.Columns.RecLevelLocP

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

structure StepCrd {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  J : Matrix (Fin n) (Fin n) X.E
  f : ℕ
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  emb : X.Tau → X.E →+* ℂ
  lat : cls → Submodule (𝓞 X.E) (Fin n → X.E)
  l0 : Submodule (𝓞 X.E) (Fin n → X.E)
  hJ : J = 1
  hf : f = X.f
  hbad : bad = plUnder X.F Pr.vGs
  hemb : emb = X.embC σ₀
  hlat : lat = L
  hl0 : l0 = stdLat X.E n

def StepCrd.std {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) : StepCrd Pr σ₀ n L :=
  ⟨1, X.f, plUnder X.F Pr.vGs, X.embC σ₀, L, stdLat X.E n, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure ClsG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E σ J T f bad
  y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Formalism.L2.Forms.Cls lev))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb
  stabI : ∀ c, stab c →* UJ (σ : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (y c).1).toMonoidHom

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def tieLev : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (fun w => (Λ w).H) (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (Ideal.absNorm_eq_natCard P.asIdeal).symm.trans (hPr.vT_norm u P hP)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

def clsG₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  y := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y
  y_bij := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_bij
  y_lat := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_lat
  stabI := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI
  stabI_inj := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_range c γ.1 γ.2

def clsG (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    ClsG hc.sig Q.J (Pr.T u) Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsG₁ hc hX hPr σ₀ u Λ c₀ s hS hs

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

def stepCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    StepCrd d.Pr d.σ₀ (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  J := CF.gramN (d.colRec a) i hi
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := CF.clsCrd (d.colRec a) u i hi
  l0 := CF.selfDualLatticeCoords (d.colRec a) i hi
  hJ := gramN_eq a hS i hi
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := funext fun c => clsCrd_eq a u i hi c
  hl0 := selfDualLatticeCoords_eq_std a hS i hi

def PtSurj (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), DecoPtSurj d.sp.cm (d.R.N i) (d.Pr.vT u) d.Pr.vGs

def stepClsG (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  clsG d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi)

def classAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.ClsTied (D := d.colRec a) u i hi where
  lev := (stepClsG a hS hH hP u i hi).lev
  y := (stepClsG a hS hH hP u i hi).y
  y_bij := (stepClsG a hS hH hP u i hi).y_bij
  y_lat := (stepClsG a hS hH hP u i hi).y_lat
  stabI := (stepClsG a hS hH hP u i hi).stabI
  stabI_inj := (stepClsG a hS hH hP u i hi).stabI_inj
  stabI_range := (stepClsG a hS hH hP u i hi).stabI_range

end Rec

end Formalism.L2.Col

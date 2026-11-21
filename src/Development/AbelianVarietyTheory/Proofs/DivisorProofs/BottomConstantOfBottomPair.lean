import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFrames
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpaceMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle Matrix
open scoped TensorProduct

variable {D : D7}

abbrev Gm (D : D7) (n : ℕ) : Type := Matrix (Fin n) (Fin n) D.host.E

abbrev UM {n : ℕ} (G : Gm D n) : Type := HA (AF D.host.F) D.sp.cm.sig G

section Pair

variable {n m : ℕ}

def mtM (G : Gm D n) (g : UM G) : Matrix (Fin n) (Fin n) (AE D) := ((HR (AF D.host.F) D.sp.cm.sig G).subtype g).1

def ratU (G : Gm D n) : Subgroup (UM G) := HFinIn (AF D.host.F) D.sp.cm.sig G

def symplM (G : Gm D n) (H : Gm D m) (x y : Mx D m n) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 *
    ∑ a, ∑ b, ∑ c, ∑ d, incA D (G⁻¹ a b) * cA D (y c b) * incA D (H c d) * x d a)

def heisM (ψ : AddChar (AF D.host.F) ℂ) (G : Gm D n) (H : Gm D m) (w₀ : Mx D m n) (f : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun w => ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplM G H w w₀) * f (w + w₀)

def ratM (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def latM (G : Gm D n) (LS : Set (Fin n → D.host.E)) (LT : Set (Fin m → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : AddSubgroup (Mx D m n) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v, ¬ P v → evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ s ∈ LS, ∃ t ∈ LT,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * G k j)}

open scoped ContDiff in

def ThetaM (ψ : AddChar (AF D.host.F) ℂ) (G : Gm D n) (H : Gm D m) (f : Mx D m n → ℂ) : Prop :=
  (∀ (γ : Matrix (Fin m) (Fin n) D.host.E) (w : Mx D m n), f (γ.map (incA D) + w) =
    ψ (-(algebraMap D.host.F (AF D.host.F) (1 / 2) * symplM G H (γ.map (incA D)) w)) * f w) ∧
  (∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisM ψ G H u f = f) ∧
  Continuous f ∧
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem theta_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T = ThetaM ψ S.gram T.gram :=
  funext fun _ => propext ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

structure WeilM (ψ : AddChar (AF D.host.F) ℂ) (G : Gm D n) (H : Gm D m) (thf : (Mx D m n → ℂ) → Prop)
    (χS χT : (AE D)ˣ →* Circle) (om : UM G × UM H →* Module.End ℂ (Mx D m n → ℂ)) : Prop where
  std : IsStdChar D ψ (-1)
  hecS : IsHeckeChar D χS
  hecT : IsHeckeChar D χT
  resS : ResEta D χS n
  resT : ResEta D χT m
  om_pres : ∀ p f, thf f → thf (om p f)
  om_heis : ∀ g h w₀ f, thf f →
    om (g, h) (heisM ψ G H w₀ f) = heisM ψ G H
      (HMul.hMul (HMul.hMul (mtM H h) (w₀ : Matrix (Fin m) (Fin n) (AE D))) (mtM G g⁻¹)) (om (g, h) f)
  om_aut : ∀ γ ∈ ratU G, ∀ γ' ∈ ratU H, ∀ f, thf f → om (γ, γ') f 0 = f 0
  om_cont : ∀ f, thf f → ∀ w, Continuous fun p : UM G × UM H => om p f w
  om_unit : ∀ (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratM D m n) 𝓕 μ → ∀ p f, thf f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  om_split : ∀ e, IsSplitIdem D e → ∀ g h, (∀ i j, (e + cA D e) * (mtM G g - 1) i j = (mtM G g - 1) i j) →
    (∀ i j, (e + cA D e) * (mtM H h - 1) i j = (mtM H h - 1) i j) → ∀ x y : (AE D)ˣ,
    (x : AE D) = e * (mtM G g).det + (1 - e) → (y : AE D) = e * (mtM H h).det + (1 - e) →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (Mx D m n → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : Mx D m n, (∀ i j, cA D e * u i j = u i j) → ∀ f, thf f → ℓ (heisM ψ G H u f) = ℓ f) →
      ∀ f, thf f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ f

theorem weil_iff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.Grid.WRep S T) :
    IsWeilDatumO ψ S T χS χT om ↔ WeilM ψ S.gram T.gram (ThetaM ψ S.gram T.gram) χS χT om := by
  rw [← theta_eq]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩⟩

def VacM (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (G : Gm D n) (H : Gm D m)
    (sS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (sT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (LS : Set (Fin n → D.host.E)) (LT : Set (Fin m → D.host.E)) (f : Mx D m n → ℂ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsVacuum (ThetaM ψ G H) (heisM ψ G H) (ratM D m n) θ (fun τ => cplxO (sS τ) (sT τ))
    (latM G LS LT fun _ => True) f

theorem vac_iff (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT LS LT f) :
    IsVacO ψ θ S T sS sT LS LT f ↔ VacM ψ θ S.gram T.gram sS sT LS LT f := by
  unfold IsVacO VacM
  rw [theta_eq]
  rfl

theorem hr_neg (G : Gm D n) : HR (AF D.host.F) D.sp.cm.sig (-G) = HR (AF D.host.F) D.sp.cm.sig G := by
  ext g
  have e : JR (F := D.host.F) (AF D.host.F) (-G) = -JR (F := D.host.F) (AF D.host.F) G := by
    ext i j; simp [JR]
  show Formalism.UG.cT _ _ * JR (F := D.host.F) (AF D.host.F) (-G) * _ = JR (F := D.host.F) (AF D.host.F) (-G) ↔
    Formalism.UG.cT _ _ * JR (F := D.host.F) (AF D.host.F) G * _ = JR (F := D.host.F) (AF D.host.F) G
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def ofNeg (G : Gm D n) : UM (-G) ≃* UM G where
  toFun g := ⟨g.1, hr_neg G ▸ g.2⟩
  invFun g := ⟨g.1, (hr_neg G).symm ▸ g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem weil_true_iff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.Grid.WRep S T) :
    GlobalTheory.Grid.IsWeil ψ true S T χS χT om ↔ WeilM ψ (-S.gram) T.gram (ThetaM ψ (-S.gram) T.gram) χS χT
      (MonoidHom.comp om ((ofNeg S.gram).toMonoidHom.prodMap (MonoidHom.id _))) :=
  weil_iff ψ (GlobalTheory.Grid.neg S) T χS χT _

end Pair

structure RigM (D : D7) (n : ℕ) where

  Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)

  β : GL (Fin n) (Lev.EAf D)

  s : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ

  B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ

def rigTo {V : HSp D} (r : Rig V) : RigM D V.rank := ⟨r.Λ, r.β, r.s, r.B⟩

def rigOf {V : HSp D} (r : RigM D V.rank) : Rig V := ⟨r.Λ, r.β, r.s, r.B⟩

def RigM.Is {n : ℕ} (G : Gm D n) (r : RigM D n) : Prop :=
  (Submodule.IsLattice D.host.E r.Λ ∧ ∀ y : Fin n → D.host.E, y ∈ r.Λ ↔
    ∀ x ∈ r.Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * G i j * y j) ∧ Formalism.L2.DIV.IsFrame r.β r.Λ ∧
    ∀ τ, IsCartanInv (G.map (tauE D τ)) (r.s τ) ∧ ∃ p, IsONBasis (G.map (tauE D τ)) (r.s τ) (r.B τ) p

def RigM.IsStd {n : ℕ} (G : Gm D n) (r : RigM D n) : Prop :=
  G = 1 ∧ (∀ y, y ∈ r.Λ ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) ∧ ∀ τ, r.s τ = 1 ∧ r.B τ = 1

def frM {n m : ℕ} (βS : GL (Fin n) (Lev.EAf D)) (βT : GL (Fin m) (Lev.EAf D)) (x : Mx D m n) :
    Matrix (Fin m) (Fin n) (Lev.EAf D) :=
  HMul.hMul (HMul.hMul (βT⁻¹).val ((x : Matrix (Fin m) (Fin n) (AE D)).map (toEAf D))) βS.val

def dualM {n m : ℕ} (G : Gm D n) (H : Gm D m) (βS : GL (Fin n) (Lev.EAf D)) (βT : GL (Fin m) (Lev.EAf D)) (x : Mx D m n) :
    Matrix (Fin n) (Fin m) (Lev.EAf D) :=
  eToEAf D D.host.xi0 • HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul ((G⁻¹).map (incA D)) ((x : Matrix (Fin m) (Fin n) (AE D)).map (cA D)).transpose)
      (H.map (incA D))).map (toEAf D)))
    βT.val

open Classical in

def fstM {n m : ℕ} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin n) (Lev.EAf D))
    (βW : GL (Fin m) (Lev.EAf D)) (x : Mx D m n) : ℂ :=
  if IsHalf e x ∧ IsIntM (frM βA βW x) ∧ ∀ i j, n ≤ i.1 → InId I (frM βA βW x i j) then
    unitChar ν e (topL n (frM βA βW x))
  else 0

open Classical in

def sndM {n m : ℕ} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (G : Gm D n) (H : Gm D m)
    (βA : GL (Fin n) (Lev.EAf D)) (βW : GL (Fin m) (Lev.EAf D)) (y : Mx D m n) : ℂ :=
  if IsHalf (cA D e) y ∧ IsIntM (dualM G H βA βW y) ∧ ∀ i j, j.1 < a → InId I (dualM G H βA βW y i j) then
    unitChar ν e (rightBlock a (dualM G H βA βW y))
  else 0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TriM (T : Type) {a a' d : ℕ} (G : Gm D a) (G' : Gm D a') (H : Gm D d) where

  rA : RigM D a

  rA' : RigM D a'

  rW : RigM D d

  om : T → UM G × UM H →* Module.End ℂ (Mx D d a → ℂ)

  om' : T → UM G' × UM H →* Module.End ℂ (Mx D d a' → ℂ)

  vac : Mx D d a → ℂ

  vac' : Mx D d a' → ℂ

  e : T → AE D

  c : T → Formalism.L2.DIV.Pl D.host.E → ℕ

  f : T → Mx D d a → ℂ

  f' : T → Mx D d a' → ℂ

  m : Measure (UM G)

  fd : Set (UM G)

  m' : Measure (UM G')

  fd' : Set (UM G')

def triTo {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) : TriM T A.gram A'.gram WW.gram :=
  ⟨rigTo X.rA, rigTo X.rA', rigTo X.rW, Tri.ω X, Tri.ω' X, X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

def triOf {T : Type} {A A' WW : HSp D} (X : TriM T A.gram A'.gram WW.gram) : Tri T A A' WW :=
  ⟨rigOf X.rA, rigOf X.rA', rigOf X.rW, X.om, X.om', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩


namespace TriM

variable {T : Type} {a a' d : ℕ} {G : Gm D a} {G' : Gm D a'} {H : Gm D d} (X : TriM T G G' H)
  (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

structure Is (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop where
  rank : a + a' = d
  rigA : X.rA.Is G
  rigA' : X.rA'.Is G'
  rigW : X.rW.Is H
  weil : ∀ t, WeilM ψ (-G) H (ThetaM ψ (-G) H) (β t) (β t / α t)
    (MonoidHom.comp (X.om t) ((ofNeg G).toMonoidHom.prodMap (MonoidHom.id _)))
  weil' : ∀ t, WeilM ψ G' H (ThetaM ψ G' H) (α t) (α t / β t) (X.om' t)
  isVac : VacM ψ θ (-G) H (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac
  isVac' : VacM ψ θ G' H X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac'
  idem : ∀ t, IsIdemSum (X.e t) (S t)
  expo : ∀ t, ∀ w ∈ S t, GlobalTheory.CMVal.ExpAt (νH t) w (X.c t w)
  fst : ∀ t, IsThetaAt ψ (symplM (-G) H) (heisM ψ (-G) H) (X.e t) (latM (-G) X.rA.Λ X.rW.Λ fun _ => True) 1 X.vac
    (fstM (α t / β t) (X.e t) (∏ w ∈ S t, w.asIdeal ^ X.c t w) X.rA.β X.rW.β) (X.f t)
  snd : ∀ t, IsThetaAt ψ (symplM G' H) (heisM ψ G' H) (cA D (X.e t)) (latM G' X.rA'.Λ X.rW.Λ fun _ => True) 1 X.vac'
    (sndM (α t / β t) (X.e t) (∏ w ∈ S t, w.asIdeal ^ X.c t w) a G' H X.rA'.β X.rW.β) (X.f' t)
  meas : X.m.IsHaarMeasure ∧ IsFundamentalDomain (ratU G) X.fd X.m
  meas' : X.m'.IsHaarMeasure ∧ IsFundamentalDomain (ratU G') X.fd' X.m'

def ker (t : T) (P : PolF D d a) (h : UM H) (g : UM G) : ℂ :=
  X.om t (g, h) (pureTensorL (aPlusAll (heisM ψ (-G) H) θ (fun τ => cplxO (-X.rA.s τ) (X.rW.s τ)) X.rA.B X.rW.B) (X.f t) P) 0

def ker' (t : T) (P : PolF D d a') (h : UM H) (g : UM G') : ℂ :=
  X.om' t (g, h) (pureTensorL (aPlusAll (heisM ψ G' H) θ (fun τ => cplxO (X.rA'.s τ) (X.rW.s τ)) X.rA'.B X.rW.B) (X.f' t) P) 0

def IsConst (c : T → ℂ) : Prop :=
  (∃ t, c t ≠ 0) ∧ ∃ (P : PolF D d a) (P' : PolF D d a'), ∀ t,
    (∀ h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m ∧ IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧
    (∃ h, ∫ g in X.fd', X.ker' ψ θ t P' h g ∂X.m' ≠ 0) ∧
    ∀ h, ∫ g in X.fd, X.ker ψ θ t P h g ∂X.m = c t * ∫ g in X.fd', X.ker' ψ θ t P' h g ∂X.m'

end TriM

theorem const_iff {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (c : T → ℂ) :
    X.IsConst ψ θ c ↔ (triTo X).IsConst ψ θ c := Iff.rfl

theorem is_iff {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) :
    X.Is ψ θ α β νH S ↔ (triTo X).Is ψ θ α β νH S :=
  ⟨fun h => ⟨h.rank, h.rigA, h.rigA', h.rigW, fun t => (weil_true_iff ψ A WW _ _ _).1 (h.weil t),
      fun t => (weil_iff ψ A' WW _ _ _).1 (h.weil' t), (vac_iff ψ θ (GlobalTheory.Grid.neg A) WW _ _ _ _ _).1 h.isVac,
      (vac_iff ψ θ A' WW _ _ _ _ _).1 h.isVac', h.idem, h.expo, h.fst, h.snd, h.meas, h.meas'⟩,
    fun h => ⟨h.rank, h.rigA, h.rigA', h.rigW, fun t => (weil_true_iff ψ A WW _ _ _).2 (h.weil t),
      fun t => (weil_iff ψ A' WW _ _ _).2 (h.weil' t), (vac_iff ψ θ (GlobalTheory.Grid.neg A) WW _ _ _ _ _).2 h.isVac,
      (vac_iff ψ θ A' WW _ _ _ _ _).2 h.isVac', h.idem, h.expo, h.fst, h.snd, h.meas, h.meas'⟩⟩

theorem move {T : Type} {a a' d b b' k : ℕ} {G : Gm D a} {G' : Gm D a'} {H : Gm D d} (X : TriM T G G' H)
    (G₁ : Gm D b) (G₁' : Gm D b') (H₁ : Gm D k) (h1 : a = b) (h2 : a' = b') (h3 : d = k) (e1 : G₁ = 1) (e2 : G₁' = 1)
    (e3 : H₁ = 1) (s1 : X.rA.IsStd G) (s2 : X.rA'.IsStd G') (s3 : X.rW.IsStd H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E))
    (hX : X.Is ψ θ α β νH S) :
    ∃ X₁ : TriM T G₁ G₁' H₁, X₁.rA.IsStd G₁ ∧ X₁.rA'.IsStd G₁' ∧ X₁.rW.IsStd H₁ ∧ X₁.Is ψ θ α β νH S ∧
      ∀ c, X₁.IsConst ψ θ c → X.IsConst ψ θ c := by
  subst h1 h2 h3
  obtain rfl : G = G₁ := s1.1.trans e1.symm
  obtain rfl : G' = G₁' := s2.1.trans e2.symm
  obtain rfl : H = H₁ := s3.1.trans e3.symm
  exact ⟨X, s1, s2, s3, hX, fun _ h => h⟩

theorem bottom_transport : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁),
    IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ X₁ : Tri T B B' WW₁, IsBottomTri W i j X₁ ∧ ∀ c : T → ℂ, X₁.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X B B' WW₁ Y hX hY
  have h1 : A.rank = B.rank := hX.rank.trans hY.rank.symm
  have h2 : A'.rank = B'.rank := hX.rank'.trans hY.rank'.symm
  have h3 : WW.rank = WW₁.rank := hX.is.rank.symm.trans (by rw [h1, h2]; exact hY.is.rank)
  obtain ⟨X₁, s1, s2, s3, hi, hc⟩ := move (triTo X) B.gram B'.gram WW₁.gram h1 h2 h3 hY.std.1 hY.std'.1 hY.stdW.1
    hX.std hX.std' hX.stdW W.ψ W.θ _ _ _ _ ((is_iff X _ _ _ _ _ _).1 hX.is)
  exact ⟨triOf X₁, ⟨hY.rank, hY.rank', s1, s2, s3, (is_iff (triOf X₁) _ _ _ _ _ _).2 hi⟩,
    fun c h => (const_iff X _ _ c).2 (hc c ((const_iff (triOf X₁) _ _ c).1 h))⟩

end GlobalTheory.SpaceMove
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁),
    IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ X₁ : Tri T B B' WW₁, IsBottomTri W i j X₁ ∧ ∀ c : T → ℂ, X₁.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  atlas_forward_decl GlobalTheory.SpaceMove.bottom_transport
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSameRig

open GlobalTheory.Grid

variable {D : D7}

theorem heisO_smul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaAt_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (ζ : ℂ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) Φ f') : f' = ζ • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) (ζ • Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }
  rw [h'.2 _ hT', hall Tm hT, LinearMap.smul_apply]

theorem isVacO_fixSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, ⟨h.2.theta.quasi, h.2.theta.level, h.2.theta.cont, h.2.theta.smooth⟩, h.2.lat, h.2.fock, h.2.norm⟩

theorem setIntegral_eq_mul {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)) (h₁ : ν₁.IsHaarMeasure)
    (h₂ : ν₂.IsHaarMeasure) (hfd₁ : IsFundamentalDomain (GQ V) fd₁ ν₁) (hfd₂ : IsFundamentalDomain (GQ V) fd₂ ν₂) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) →
      (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hpos.ne', fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]

set_option maxHeartbeats 1000000 in

theorem const_of_sameRig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X Y hX hY hA hA' hW c hc

  have hvX := hX.is.isVac
  have hvY := hY.is.isVac
  rw [← hA, ← hW] at hvY
  have hvX' := hX.is.isVac'
  have hvY' := hY.is.isVac'
  rw [← hA', ← hW] at hvY'
  have hψ : IsStdChar D W.ψ (-1) := hvX.1
  have hθ : IsInfFam W.θ := hvX.2.inf
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hcS' : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig (neg A))
    (Formalism.L2.Fam.ThC.fixSig WW) (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS hcT X.rA.Λ X.rW.Λ (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1 X.vac Y.vac (isVacO_fixSig hvX)
    (isVacO_fixSig hvY)
  obtain ⟨ζ', hζ1', hζ'⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig A')
    (Formalism.L2.Fam.ThC.fixSig WW) X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS' hcT X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac' Y.vac' (isVacO_fixSig hvX') (isVacO_fixSig hvY')
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζ0' : ζ' ≠ 0 := fun h => by rw [h, norm_zero] at hζ1'; exact zero_ne_one hζ1'

  have he : ∀ t, Y.e t = X.e t := fun t => GlobalTheory.BaseKernelUniq.idemSum_unique A (hY.is.idem t) (hX.is.idem t)
  have hid : ∀ t, Y.ideal (locPl G) t = X.ideal (locPl G) t := fun t => by
    unfold Tri.ideal
    exact Finset.prod_congr rfl fun w hw => by rw [(hY.is.expo t w hw).unique (hX.is.expo t w hw)]

  have hf : ∀ t, Y.f t = ζ • X.f t := fun t => by
    have h2 := hY.is.fst t
    rw [← hA, ← hW, he t, hid t, hζ] at h2
    exact thetaAt_smul (S := neg A) ζ (hX.is.fst t) h2
  have hf' : ∀ t, Y.f' t = ζ' • X.f' t := fun t => by
    have h2 := hY.is.snd t
    rw [← hA', ← hW, he t, hid t, hζ'] at h2
    exact thetaAt_smul ζ' (hX.is.snd t) h2

  have thX : ∀ t, IsThetaFunO W.ψ (neg A) WW (X.f t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.fst t) hvX.2.theta
  have thX' : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.snd t) hvX'.2.theta

  have hk : ∀ t P h g, Y.ker W.ψ W.θ t P h g = ζ * X.ker W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have hWY : IsWeilDatumO W.ψ (neg A) WW _ _ ((Y.ω t).toSgn true) := hY.is.weil t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ (neg A) WW _ _ _ _ hWY hWX ((ofSgn true A).symm g, h) _ hF
    unfold Tri.ker
    rw [← hA, ← hW, hf t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show ((Y.ω t).toSgn true) ((ofSgn true A).symm g, h) (ζ • _) 0 =
      ζ * ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hk' : ∀ t P h g, Y.ker' W.ψ W.θ t P h g = ζ' * X.ker' W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have hWY : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hY.is.weil' t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ A' WW _ _ _ _ hWY hWX (g, h) _ hF
    unfold Tri.ker'
    rw [← hA', ← hW, hf' t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show (Y.ω' t) (g, h) (ζ' • _) 0 = ζ' * (X.ω' t) (g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]

  have inv : ∀ t P h, ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have e1 : (((ofSgn true A).symm (γ * g), h) : GA D (neg A) × GA D WW) =
        ((ofSgn true A).symm γ, 1) * ((ofSgn true A).symm g, h) := by simp
    show ((X.ω t).toSgn true) ((ofSgn true A).symm (γ * g), h) _ 0 = ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hWX.om_pres _ _ hF)
  have inv' : ∀ t P h, ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have e1 : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
    show (X.ω' t) (γ * g, h) _ 0 = (X.ω' t) (g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ hγ 1 (one_mem _) _ (hWX.om_pres _ _ hF)

  obtain ⟨r, hr0, hr⟩ := setIntegral_eq_mul X.m Y.m X.fd Y.fd hX.is.meas.1 hY.is.meas.1 hX.is.meas.2 hY.is.meas.2
  obtain ⟨r', hr0', hr'⟩ := setIntegral_eq_mul X.m' Y.m' X.fd' Y.fd' hX.is.meas'.1 hY.is.meas'.1 hX.is.meas'.2
    hY.is.meas'.2
  have hYk : ∀ t P h, Y.ker W.ψ W.θ t P h = fun g => ζ * X.ker W.ψ W.θ t P h g := fun t P h => funext (hk t P h)
  have hYk' : ∀ t P h, Y.ker' W.ψ W.θ t P h = fun g => ζ' * X.ker' W.ψ W.θ t P h g := fun t P h => funext (hk' t P h)
  have hI : ∀ t P h, X.I W.ψ W.θ t P h = r * ζ⁻¹ * Y.I W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I, Tri.I, hYk, integral_const_mul, (hr _ (inv t P h)).2]
    field_simp
  have hI' : ∀ t P h, X.I' W.ψ W.θ t P h = r' * ζ'⁻¹ * Y.I' W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I', Tri.I', hYk', integral_const_mul, (hr' _ (inv' t P h)).2]
    field_simp
  have hint : ∀ t P h, IntegrableOn (Y.ker W.ψ W.θ t P h) Y.fd Y.m → IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m :=
    fun t P h hi => by
      rw [hYk, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0)] at hi
      exact (hr _ (inv t P h)).1.2 hi
  have hint' : ∀ t P h, IntegrableOn (Y.ker' W.ψ W.θ t P h) Y.fd' Y.m' →
      IntegrableOn (X.ker' W.ψ W.θ t P h) X.fd' X.m' := fun t P h hi => by
    rw [hYk', IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0')] at hi
    exact (hr' _ (inv' t P h)).1.2 hi

  set κ : ℂ := r * ζ⁻¹ * (r' * ζ'⁻¹)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero hζ0)) (inv_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')))
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := hc
  have hX1 : X.IsConst W.ψ W.θ fun t => κ * c t := by
    refine ⟨⟨t₁, mul_ne_zero hκ0 h₁⟩, P, P', fun t => ⟨fun h => ⟨hint t P h ((H t).1 h).1, hint' t P' h ((H t).1 h).2⟩,
      ?_, fun h => ?_⟩⟩
    · obtain ⟨h, hh⟩ := (H t).2.1
      refine ⟨h, ?_⟩
      rw [hI']
      exact mul_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')) hh
    · have e := (H t).2.2 h
      have e' : Y.I' W.ψ W.θ t P' h = (r' * ζ'⁻¹)⁻¹ * X.I' W.ψ W.θ t P' h := by
        rw [hI', ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0' (inv_ne_zero hζ0')), one_mul]
      rw [hI, e, e', hκ]
      ring
  have := GlobalTheory.BotTransfer.isConst_smul hX1 (inv_ne_zero hκ0)
  simpa only [← mul_assoc, inv_mul_cancel₀ hκ0, one_mul] using this

end GlobalTheory.BotSameRig
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  atlas_forward_decl GlobalTheory.BotSameRig.const_of_sameRig
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

theorem bottom_const_transfer : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S hψ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨X₁, hX₁, hX₁c⟩ := GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants W i j A A' WW X B B' WW₁ Y hX hY
  obtain ⟨Y₁, hY₁, e1, e2, e3, hY₁c⟩ := GlobalTheory.T.exists_definiteBottomTriple_transferred_frames W S hψ μ₀ hL hN i j B B' WW₁ X₁ Y hX₁ hY
  obtain ⟨u, hu⟩ := hY₁c c hc
  exact ⟨u, hX₁c _ (GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices W i j B B' WW₁ X₁ Y₁ hX₁ hY₁ e1.symm e2.symm e3.symm _ hu)⟩

end GlobalTheory.BotTransfer
end

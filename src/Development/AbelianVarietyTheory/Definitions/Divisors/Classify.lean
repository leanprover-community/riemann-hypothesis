import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKP

structure Raw (K R : Type) [Field K] [Ring R] [Algebra ℚ R] where

  A : AbVar K

  ia : R →ₐ[ℚ] End0 A

  L : LB A.X.left
  hL : L.IsLB

section General

variable {K R : Type} [Field K] [Ring R] [Algebra ℚ R]

def Raw.c (X : Raw K R) : Pic X.A.X.left := cls X.L X.hL

def IsPol (σ : R → R) (X : Raw K R) : Prop :=
  IsAmpleCls X.c ∧ ∀ r : End0 X.A →ₗ[ℚ] End0 X.A, IsRosati X.c r → ∀ x, r (X.ia x) = X.ia (σ x)

def Intertw {A B : AbVar K} (f : A ⟶ B) (a : End0 A) (b : End0 B) : Prop :=
  ∀ (n : ℤ) (g : End A) (h : End B), n • a = toEnd0 A g → n • b = toEnd0 B h →
    (show A ⟶ A from g) ≫ f = f ≫ (show B ⟶ B from h)

def IsRIsog {A B : AbVar K} (a : R →ₐ[ℚ] End0 A) (b : R →ₐ[ℚ] End0 B) (f : A ⟶ B) : Prop :=
  IsIsogeny f ∧ ∀ x, Intertw f (a x) (b x)

def PolIsog (X Y : Raw K R) : Prop :=
  ∃ (f : X.A ⟶ Y.A) (m n : ℕ), IsRIsog X.ia Y.ia f ∧ 0 < m ∧ 0 < n ∧
    m • AbVar.lam X.c (fst X.A.X X.A.X) (snd X.A.X X.A.X) =
      n • AbVar.lam Y.c (fst X.A.X X.A.X ≫ f.hom) (snd X.A.X X.A.X ≫ f.hom)

def Betti (X : Raw K R) {W : Type} [AddCommGroup W] [Module ℚ W] (ρ : R → W → W) (ψ : W → W → ℚ) : Prop :=
  ∃ (Λ : Submodule ℤ W) (s : ℚ), Λ.FG ∧ Submodule.span ℚ (Λ : Set W) = ⊤ ∧ 0 < s ∧
    (∀ v ∈ Λ, ∀ w ∈ Λ, ∃ a : ℤ, s * ψ v w = a) ∧
    ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
      ∃ (β : Λ →ₗ[ℤ] Tl l X.A) (ζ : Tate l (AlgebraicClosure K)ˣ),
        Function.Bijective (β.liftBaseChange ℤ_[l]) ∧ Submodule.span ℤ_[l] {ζ} = ⊤ ∧
        (∀ (x : R) (n : ℤ) (g : End X.A) (v w : Λ), n • X.ia x = toEnd0 X.A g → n • ρ x v = (w : W) →
          tend l X.A g (β v) = β w) ∧
        ∀ E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ, IsWeilForm l X.L E →
          ∀ (v w : Λ) (a : ℤ), s * ψ v w = a → E (β v) (β w) = a • ζ

def Link {K' : Type} [Field K'] (X : Raw K R) (Y : Raw K' R) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (l : K') ≠ 0 →
    ∃ (e : Tl l X.A ≃ₗ[ℤ_[l]] Tl l Y.A)
      (u : Tate l (AlgebraicClosure K)ˣ ≃ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
      (∀ (x : R) (n : ℤ) (g : End X.A) (h : End Y.A), n • X.ia x = toEnd0 X.A g → n • Y.ia x = toEnd0 Y.A h →
        ∀ t, e (tend l X.A g t) = tend l Y.A h (e t)) ∧
      ∀ (E : Tl l X.A →ₗ[ℤ_[l]] Tl l X.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K)ˣ)
        (E' : Tl l Y.A →ₗ[ℤ_[l]] Tl l Y.A →ₗ[ℤ_[l]] Tate l (AlgebraicClosure K')ˣ),
        IsWeilForm l X.L E → IsWeilForm l Y.L E' → ∀ s t, E' (e s) (e t) = u (E s t)

def IsTwist {A : AbVar K} (c d : Pic A.X.left) (h : End0 A) : Prop :=
  ∃ (n m : ℕ) (g : End A), 0 < n ∧ 0 < m ∧ (m : ℤ) • h = toEnd0 A g ∧
    IsAdj (A := A) (B := A) c d (𝟙 A) n g

def IsFrobModel (q : ℕ) (A : AbVar K) (φ : End A) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k) (_ : Algebra k K) (A₀ : AbVar k) (e : baseChange K A₀ ≅ A),
    Fintype.card k = q ∧ (show A ⟶ A from φ) = e.inv ≫ bcMap K (A := A₀) (B := A₀) (frob A₀) ≫ e.hom

def PInt (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ N : ℕ, ¬ p ∣ N ∧ IsIntegral ℤ (N • x)

def PUnit (p : ℕ) {D : Type} [Ring D] (x : D) : Prop := ∃ u : Dˣ, (u : D) = x ∧ PInt p x ∧ PInt p ((u⁻¹ : Dˣ) : D)

def FrobLike (p r : ℕ) (A : AbVar K) (π : End0 A) : Prop :=
  ∃ (m : ℕ) (φ : End A) (u : End0 A), 0 < m ∧ IsFrobModel (p ^ (r * m)) A φ ∧ Commute π (toEnd0 A φ) ∧
    PUnit p u ∧ π ^ m = u * toEnd0 A φ

end General

abbrev Fb (p : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (ZMod p)

abbrev Zb : Type := integralClosure ℤ ℂ

section CM

variable {M : Type} [Field M] [NumberField M]

def intEmb (φ : M →+* ℂ) : 𝓞 M →+* Zb :=
  (φ.comp (algebraMap (𝓞 M) M)).codRestrict (integralClosure ℤ ℂ) fun x =>
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (RingHom.id ℤ) φ (RingHom.ext_int _ _)

def IsCMType (Φ : Finset (M →+* ℂ)) : Prop := ∀ φ, φ ∈ Φ ↔ ComplexEmbedding.conjugate φ ∉ Φ

def Matches (p r : ℕ) {k : Type} [Field k] (j : Zb →+* k) (Φ : Finset (M →+* ℂ)) (π : M) : Prop :=
  π ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 M)) (m : ℤ), (p : 𝓞 M) ∈ w.asIdeal →
    w.valuation M π = WithZero.exp (-m) →
      (Ideal.absNorm w.asIdeal : ℚ) ^ m =
        (p : ℚ) ^ (r * Nat.card {φ : Φ // RingHom.ker (j.comp (intEmb φ.1)) = w.asIdeal})

def HasInt {K : Type} [Field K] (X : Raw K M) (a : OAct (𝓞 M) X.A.X) : Prop :=
  ∀ x : 𝓞 M, ∃ g : End X.A, AbVar.Hom.hom g = a.act x ∧ X.ia x = toEnd0 X.A g

def IsCMLie {K : Type} [Field K] (X : Raw K M) {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → 𝓞 M →+* K) : Prop :=
  2 * X.A.dim = Module.finrank ℚ M ∧ ∃ a : OAct (𝓞 M) X.A.X, HasInt X a ∧ IsLieType a φ

variable [IsCMField M]

def cj (x : M) : M := IsCMField.complexConj M x

def TotPos (h : M) : Prop := cj h = h ∧ ∀ φ : M →+* ℂ, 0 < (φ h).re

def PosXi (Φ : Finset (M →+* ℂ)) (ξ : M) : Prop := cj ξ = -ξ ∧ ∀ φ ∈ Φ, 0 < (φ ξ).im

def sigH {d : ℕ} (H : Fin d → M) (x : Matrix (Fin d) (Fin d) M) : Matrix (Fin d) (Fin d) M :=
  Matrix.of fun i j => (H i)⁻¹ * cj (x j i) * H j

def psiH {d : ℕ} (H : Fin d → M) (ξ : M) (v w : Fin d → M) : ℚ :=
  Algebra.trace ℚ M (ξ * ∑ i, H i * v i * cj (w i))

def psi1 (ξ v w : M) : ℚ := Algebra.trace ℚ M (ξ * (v * cj w))

def XiEquiv (ξ ξ' : M) : Prop := ∃ (c : ℚ) (x : M), 0 < c ∧ x ≠ 0 ∧ ξ' = c * (x * cj x) * ξ

def admitted (p r : ℕ) {K : Type} [Field K] {d : ℕ} (H : Fin d → M) (π : M)
    (X : Raw K (Matrix (Fin d) (Fin d) M)) : Prop :=
  IsPol (sigH H) X ∧ 2 * X.A.dim = d * Module.finrank ℚ M ∧
    FrobLike p r X.A (X.ia (Matrix.scalar (Fin d) π))

end CM

def ClassifyField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (M : Type) [Field M] [NumberField M] [IsCMField M] (d : ℕ) (H : Fin d → M)
    (Φ : Finset (M →+* ℂ)) (j : Zb →+* Fb p) (π : M), 0 < r → 0 < d → (∀ i, TotPos (H i)) → IsCMType Φ →
    Matches p r j Φ π →
    ∃ X : {ξ : M // PosXi Φ ξ} → Raw (Fb p) (Matrix (Fin d) (Fin d) M),
      (∀ ξ, admitted p r H π (X ξ) ∧ Betti (X ξ) Matrix.mulVec (psiH H ξ.1)) ∧
      (∀ Y, admitted p r H π Y → ∃ ξ, PolIsog Y (X ξ)) ∧
      ∀ ξ ξ', PolIsog (X ξ) (X ξ') ↔ XiEquiv ξ.1 ξ'.1

end GlobalTheory.LKP
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

section Points

variable {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ} (L : Link D G)

def actHom (o : Obj b N (spMap β)) : D.O →+* End (av o) :=
  RingHom.mk' ⟨⟨actEnd o, Subtype.ext o.act.one⟩, fun x y => Subtype.ext (o.act.mul x y)⟩
    (fun x y => Subtype.ext (o.act.add x y))

def PairIso (o : Obj b N (spMap β)) (π : End0 (av o)) (o' : Obj b N (spMap β)) (π' : End0 (av o')) : Prop :=
  ∃ (m : ObjMap o o' (𝟙 _)) (e : av o ≅ av o'), (AbVar.Hom.hom e.hom).left = m.φ ∧ GlobalTheory.LKP.Intertw e.hom π π'

def PairIsog (o : Obj b N (spMap β)) (π : End0 (av o)) (o' : Obj b N' (spMap β)) (π' : End0 (av o')) : Prop :=
  ∃ (I : TIso o) (I' : TIso o') (ψ : av o ⟶ av o') (g : G.GAf),
    IsIsogeny ψ ∧ Acts L I I' ψ 1 g ∧ GlobalTheory.LKP.Intertw ψ π π'

def raw {A : Type} [Ring A] [Algebra ℚ A] (o : Obj b N (spMap β)) (ia : A →ₐ[ℚ] End0 (av o)) : GlobalTheory.LKP.Raw k A where
  A := av o
  ia := ia
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  hL := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull o.isLB _

variable [CharP k p] [PerfectRing k p]

abbrev OFrame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (o : Obj b N (spMap β)) (π : End0 (av o))
    (H : PDivGroup p k) (t : H.TorsionTower (av o).X) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) : Type :=
  Frame L T red r H (fun c => t.map t (actEnd o c).hom)
    (fun m ψ => ∃ g : End (av o), m • π = toEnd0 _ g ∧ ψ = t.map t g.hom) d

def RowRel (r : ℕ) (w : Fin G.m) (c : ℤ) (u : GL (Fin G.n) (KQ p (G.Fw w) r))
    (X Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r)) : Prop :=
  Y.map (intKQ p (G.Fw w) r).subtype =
    c • HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      (X.map (intKQ p (G.Fw w) r).subtype) u.val

structure Based (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (P : Pair G) (o : Obj b N (spMap β))
    (π : End0 (av o)) where

  I : TIso o
  ind : Induces o I

  x : (AfP p ⊗[ℚ] G.C)ˣ

  s : (AfP p)ˣ
  hx : Triv G (AfP p) P.β x s

  δ : Gr G r

  z : Gr G r
  nrm : IsNrm G r P.atP δ z
  supp : L.MuSupp r δ

  j : P.cent →* (End0 (av o))ˣ
  j_self : (j P.self : End0 (av o)) * π = 1
  j_af : ∀ y, ActsQ L I (j y : End0 (av o)) (P.toAf x s hx y)
  j_surj : ∀ u : End0 (av o), Commute u π → (∃ g, ActsQ L I u g) → ∃ y, (j y : End0 (av o)) = u

  H : PDivGroup p k

  t : H.TorsionTower (av o).X

  fr : OFrame L T red r o π H t δ.2
  j_p : ∀ y (m : ℤ) (ψ : End (av o)), m • (j y : End0 (av o)) = toEnd0 _ ψ → ∀ w X Y,
    RowRel r w m ((P.toQr r z y).2 w) X Y → T.map (t.map t ψ.hom) (fr.B w X) = fr.B w Y

variable {L}

def Based.ga {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {P : Pair G} {o : Obj b N (spMap β)}
    {π : End0 (av o)} (B : Based L T red r P o π) : G.GAf := P.toAf B.x B.s B.hx P.self

def Based.Coord {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {P : Pair G} {o : Obj b N (spMap β)}
    {π : End0 (av o)} (B : Based L T red r P o π) (o' : Obj b N (spMap β)) (π' : End0 (av o')) (g : G.GAf)
    (y : Gr G r) : Prop :=
  ∃ (I' : TIso o') (ψ : av o ⟶ av o') (m : ℕ) (v : ℤ) (H' : PDivGroup p k) (t' : H'.TorsionTower (av o').X)
    (fr' : OFrame L T red r o' π' H' t' (y⁻¹ * B.δ * sigG G r y).2),
    0 < m ∧ Induces o' I' ∧ IsIsogeny ψ ∧ Acts L B.I I' ψ m g⁻¹ ∧ GlobalTheory.LKP.Intertw ψ π π' ∧
    fr'.sp = B.fr.sp ∧
    (∀ w (c : ℤ) X Y, RowRel r w c (y.2 w)⁻¹ X Y →
      c • T.map (B.t.map t' ψ.hom) (fr'.B w X) = (m : ℤ) • B.fr.B w Y) ∧
    GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r y.1 v ∧
    (padicValNat p (deg ψ) : ℤ) = (av o).dim * (2 * padicValNat p m - v)

end Points

def Live (L : Link D G) (r : ℕ) (P : Pair G) : Prop := ∃ δ z, IsNrm G r P.atP δ z ∧ L.MuSupp r δ

def JCompat (G : HTGroup p) {k : Type} [Field k] (red : (Obar p).toSubring →+* k) (j : GlobalTheory.LKP.Zb →+* k) : Prop :=
  ∀ (a : AlgebraicClosure ℚ) (z : GlobalTheory.LKP.Zb) (z' : (Obar p).toSubring), G.iotaC a = z → G.iotaP a = z' → j z = red z'

structure Chart (L : Link D G) (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra G.F M] where
  rank : Module.finrank G.F M = G.n

  i : M →ₐ[G.F] G.C

  H : Fin G.n → M
  pos : ∀ a, GlobalTheory.LKP.TotPos (H a)

  κ : VQ D ≃ₗ[ℚ] (Fin G.n → M)
  κ_i : ∀ x v, κ (L.rep (i x) v) = x • κ v

  oM : D.O →+* Matrix (Fin G.n) (Fin G.n) M
  κ_o : ∀ c v, κ (actQ D c v) = oM c *ᵥ κ v
  span : Submodule.span M (Set.range oM) = ⊤
  star : ∀ c, oM (D.star c).unop = GlobalTheory.LKP.sigH H (oM c)

namespace Chart

variable {L : Link D G} {M : Type} [Field M] [NumberField M] [IsCMField M] [Algebra G.F M] (ch : Chart L M)

def FormOf (β : G.Cˣ) (ξ : M) : Prop :=
  ∀ v w, D.EF.baseChange ℚ v (L.rep ((β⁻¹ : G.Cˣ) : G.C) w) = -GlobalTheory.LKP.psiH ch.H ξ (ch.κ v) (ch.κ w)

def IsRaw {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N : ℕ} (a : M)
    (o : Obj b N (spMap β)) (π : End0 (av o)) (ia : Matrix (Fin G.n) (Fin G.n) M →ₐ[ℚ] End0 (av o)) : Prop :=
  (∀ c, ia (ch.oM c) = toEnd0 _ (actEnd o c)) ∧ ia (Matrix.scalar _ a) * π = 1

end Chart

def typeOf (L : Link D G) (M : Type) [Field M] [NumberField M] [Algebra G.F M] (φ₀ : M →+* ℂ) : Finset (M →+* ℂ) :=
  insert φ₀ (Finset.univ.filter fun φ => φ (algebraMap G.F M (L.e D.ω)) = (starRingEnd ℂ) D.ρc ∧
    φ ≠ ComplexEmbedding.conjugate φ₀)

def MarkAt (L : Link D G) {M : Type} [Field M] [Algebra G.F M] (φ₀ : M →+* ℂ) (a : M) (mu : ℂ) : Prop :=
  ∃ i : Fin D.a, φ₀.comp (algebraMap G.F M) = G.iotaC.comp (L.s i) ∧
    mu = if (InfinitePlace.mk (G.iotaC.comp (L.s i))).embedding = G.iotaC.comp (L.s i) then φ₀ a
      else (starRingEnd ℂ) (φ₀ a)

def Classify : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R]
    (b : Base D R) (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p))
    (N r : ℕ), Setup L b β red N r → ∀ sel, L.GoodSel sel →
    ∃ (o : {q : Cls G // (Quot.out q).Mark (sel (Quot.out q).pol) ∧ Live L r (Quot.out q)} → Obj b N (spMap β))
      (π : ∀ q, End0 (av (o q))),
      (∀ q, Nonempty (Based L T red r (Quot.out q.1) (o q) (π q))) ∧
      ∀ (o' : Obj b N (spMap β)) (π' : End0 (av o')) ga δ, IsPair L T red r o' π' ga δ → L.MuSupp r δ → RegAf G ga →
        ∃! q, PairIsog L (o q) (π q) o' π'

end GlobalTheory.LKGeo
end
end

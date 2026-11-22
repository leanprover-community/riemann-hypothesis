module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

structure Amb (l : ℕ) [Fact l.Prime] where
  K : Type
  [fK : Field K]
  [ac : IsAlgClosed K]
  V : ValuationSubring K
  a : ∀ c : Coef l, c.O →+* V
  compat : ∀ (c c' : Coef l) (h : c.O ≤ c'.O) (x : c.O), a c' (Subalgebra.inclusion h x) = a c x
  loc : ∀ c, IsLocalHom (a c)
  alg : ∀ x : V, ∃ (c : Coef l) (y : c.O), x - a c y ∈ maximalIdeal V

attribute [instance] Amb.fK Amb.ac Amb.loc

abbrev inc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : c.O →+* c'.O := (Subalgebra.inclusion h : c.O →ₐ[ℤ_[l]] c'.O)

namespace Amb

variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)

abbrev k : Type := ResidueField 𝔞.V

abbrev red (c : Coef l) : c.O →+* 𝔞.k := (residue 𝔞.V).comp (𝔞.a c)

def j (c : Coef l) : ResidueField c.O →+* 𝔞.k := ResidueField.map (𝔞.a c)

abbrev toK : 𝔞.V →+* 𝔞.K := 𝔞.V.subtype

def IsZero (e : 𝔞.K ≃+* PadicAlgCl l) : Prop := (∀ c x, e (𝔞.a c x) = x) ∧ ∀ x, x ∈ 𝔞.V ↔ ‖e x‖ ≤ 1

structure IsDvr {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V) : Prop where
  inj : Function.Injective f
  loc : IsLocalHom f
  complete : IsAdicComplete (maximalIdeal A) A
  fin : Finite (ResidueField A)
  alg : ∀ x : 𝔞.K, ∃ p : A[X], p ≠ 0 ∧ p.eval₂ (𝔞.toK.comp f) x = 0

def Small {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (P : PD ι Γ 𝔞.V) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (P₁ : PD ι Γ A),
    𝔞.IsDvr f ∧ P₁.Cont (maximalIdeal A) ∧ P₁.map f = P

end Amb

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def Ctx2 (D : Raw Ω c) : Prop :=
  D.Good ∧ ∃ (h : Host) (t e : ℕ) (ψ : DirichletCharacter c.O h.N), h.Big t ∧ 0 < e ∧ e < t ∧ ψ ∈ h.X c e ∧
    h.CaseII l e ψ ∧ Aut.OfChar D e ψ (h.nII l ψ) 1 1

def Ctx3 (D : Raw Ω c) : Prop :=
  D.Good ∧ ∃ (h : Host) (t e : ℕ) (ψ : DirichletCharacter c.O h.N), h.Big t ∧ 0 < e ∧ e < t ∧ ψ ∈ h.X c e ∧
    h.CaseIII l e ψ ∧ Aut.OfChar D e ψ (h.nIII l ψ) (pOne h.chi) (orderOf ψ)

structure KPair (D : Raw Ω c) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) (u : M4 𝔞.V) : Prop where
  small : 𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _)
  red : ∀ g i j, r g i j - 𝔞.a c (D.r0 g i j) ∈ maximalIdeal 𝔞.V
  mult : ∀ g, IsGSp (𝔞.a c (D.th g)) (r g)
  unr : D.UnrT r 1
  atP : ∀ p ∈ D.Sb, ∀ g ∈ D.Ip p ⊓ D.ψ.ker, r g = 1
  sp : IsGSp 1 u
  flag : ∀ s ∈ D.Gp l, IsUp (adj u * r s * u)
  char : ∀ s ∈ D.Gp l, ∀ i, (adj u * r s * u) i i - 𝔞.a c (D.ps i s) ∈ maximalIdeal 𝔞.V
  inert : ∀ s ∈ D.Ip l, ∀ i, (adj u * r s * u) i i = 𝔞.a c (D.ps i s)

def Con (D : Raw Ω c) : Prop :=
  ∀ 𝔞 : Amb l, CharP 𝔞.K l → ∀ r u, KPair D 𝔞 r u → ¬ Star (mapRep 𝔞.toK r)

def VPt (D : Raw Ω c) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  𝔞.Small (⟨r, fun _ => 1⟩ : PD Unit _ _) ∧
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R) (y : R →+* 𝔞.V),
      D.IsPt ρ ∧ y.comp (algebraMap c.O R) = 𝔞.a c ∧ (∀ x ∈ maximalIdeal R, y x ∈ maximalIdeal 𝔞.V) ∧ r = mapRep y ρ.hom

abbrev resQ (F : IntermediateField ℚ Ω) : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

def resLe {F L : IntermediateField ℚ Ω} (h : F ≤ L) : G L Ω →* G F Ω where
  toFun g := { g.toRingEquiv with commutes' := fun x => g.commutes ⟨x.1, h x.2⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

def lab (pr : Bool) : Fin 4 → Fin 4 := if pr then ![2, 3, 0, 1] else id

def chi (D : Raw Ω c) (pr : Bool) (i : Fin 4) : G ℚ Ω →* c.Oˣ := D.ps (lab pr i)

def LabOk (D : Raw Ω c) (pr : Bool) : Prop := pr = true → ∀ s ∈ D.Gp l, Raw.bar D.Psi s = 1

def frQ (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) : Fr c.O (G ℚ Ω) where
  ι := Unit
  Gv _ := D.Gp l
  Iv _ := D.Ip l
  Mu _ := ∅
  N := {g | (∃ A, Raw.Away D.T A ∧ g ∈ Ine (F := ℚ) A ∧ D.rbar g = 1) ∨ ∃ p ∈ D.Sb, g ∈ D.Ip p ⊓ D.ψ.ker}
  χ := chi D pr
  ν := D.th
  g0 := g0

structure QPair (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V) : Prop where
  small : 𝔞.Small P
  pair : (frQ D pr g0).IsPair (𝔞.a c) P
  inert : ∀ s ∈ D.Ip l, ∀ i, P.ψ () i s = 𝔞.a c (D.ps i s)

structure NearSplit (D : Raw Ω c) (pr : Bool) (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V) : Prop where
  red : ∀ g i j, P.r g i j - 𝔞.a c (diagRep (chi D pr) g i j) ∈ maximalIdeal 𝔞.V
  flag : ∀ i j, i ≠ j → wt i j ≠ -wPs → P.n () i j ∈ maximalIdeal 𝔞.V
  char : ∀ s ∈ D.Gp l, ∀ i, P.ψ () i s - 𝔞.a c (chi D pr i s) ∈ maximalIdeal 𝔞.V

structure LatShape (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) {k : Type} [Field k] (a : c.O →+* k)
    (P : PD Unit (G ℚ Ω) k) : Prop where
  res : (frQ D pr g0).IsRes a P
  supp : Supp nP P.r
  flag : SuppM qQ (P.n ())
  be : Ent P.r wBe
  ps : Ent P.r (-wPs) ∨ (Supp vV P.r ∧ P.n () 2 0 ≠ 0 ∧ (∀ s ∈ D.Gp l, Raw.bar D.Psi s = 1) ∧
    ¬ ∃ m : k, ∀ s ∈ D.Gp l, P.r s 1 2 = m * (a (chi D pr 2 s) - a (chi D pr 1 s)))

def Over {F F' : Type} [Field F] [Field F'] [Algebra F Ω] [Algebra F' Ω] (φ : G F' Ω →* G F Ω) {ι ι' R : Type} [CommRing R]
    (pl : ι → ValuationSubring Ω) (pl' : ι' → ValuationSubring Ω) (P : PD ι (G F Ω) R) (P' : PD ι' (G F' Ω) R) : Prop :=
  P'.r = P.r.comp φ ∧ ∀ v', ∃ (v : ι) (g : G F Ω), (∀ x, g x ∈ pl' v' ↔ x ∈ pl v) ∧ IsUp (adj (P'.n v') * P.r g * P.n v)

structure Tower (D : Raw Ω c) where
  pr : Bool
  K : IntermediateField ℚ Ω
  F : IntermediateField ℚ Ω
  L : IntermediateField ℚ Ω
  [nK : NumberField K]
  [nF : NumberField F]
  [nL : NumberField L]
  [cmK : IsCMField K]
  [realF : IsTotallyReal F]
  [cmL : IsCMField L]
  [abF : IsAbelianGalois ℚ F]
  degK : Module.finrank ℚ K = 2
  hL : L = F ⊔ K
  g0 : G F Ω
  ι : Type
  [fin : Finite ι]
  pl : ι → ValuationSubring Ω
  ovl : ∀ v, (pl v).valuation (l : Ω) < 1
  cover : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃! v, ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ pl v
  one : ∀ v, ∀ x ∈ K, x ∈ pl v ↔ x ∈ D.pl l

attribute [instance] Tower.nK Tower.nF Tower.nL Tower.cmK Tower.realF Tower.cmL Tower.abF Tower.fin

def TameL (l : ℕ) (F : IntermediateField ℚ Ω) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, ∃ m : ℕ, l.Coprime m ∧ g ^ m ∈ F.fixingSubgroup

variable (l) in
def IsLayer (m : ℕ) (F F' : IntermediateField ℚ Ω) : Prop :=
  ∀ g : G ℚ Ω, g ∈ F'.fixingSubgroup ↔ g ∈ F.fixingSubgroup ∧ cycZ ℚ Ω l g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (m + 1)

variable (l) in
def Dies (w : ℕ) (F : IntermediateField ℚ Ω) : Prop :=
  ∀ θ : G ℚ Ω →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (G ℚ Ω)) →
    (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) → F.fixingSubgroup ≤ θ.ker

namespace Tower

variable {D : Raw Ω c} (T : Tower D)

theorem F_le : T.F ≤ T.L := T.hL ▸ le_sup_left

abbrev d : ℕ := Module.finrank ℚ T.F

def GalL : Subgroup (G T.F Ω) := T.K.fixingSubgroup.comap (resQ T.F)

def G' : Subgroup (G T.F Ω) := T.GalL ⊓ (cycZ T.F Ω l).ker

def fr (W : Finset ℕ) : Fr c.O (G T.F Ω) where
  ι := T.ι
  Gv v := Dec (F := T.F) (T.pl v)
  Iv v := Ine (F := T.F) (T.pl v)
  Mu v := muOf l (Dec (F := T.F) (T.pl v))
  N := {g | ∃ A, Raw.Away (insert l W) A ∧ g ∈ Ine (F := T.F) A ∧ D.rbar (resQ T.F g) = 1}
  χ i := (chi D T.pr i).comp (resQ T.F)
  ν := D.th.comp (resQ T.F)
  g0 := T.g0

abbrev rb (w : ℤ × ℤ) (g : G T.F Ω) : ResidueField c.O := residue c.O ((T.fr ∅).rt w g : c.O)

def U1 (v : T.ι) : Set (G T.F Ω) :=
  {s | s ∈ Ine (F := T.F) (T.pl v) ∧ cycZ T.F Ω l s = 1 ∧ D.rbar (resQ T.F s) = 1}

def Splits (w : ℕ) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ T.F.fixingSubgroup ⊓ D.rbar.ker ⊓ D.om.ker

structure Ok : Prop where
  lab : LabOk D T.pr
  even : Even T.d
  unr : ∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL
  split : ∀ p ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ T.K.fixingSubgroup
  g2 : ∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)
  g3 : ∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1
  g3' : ∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) →
    (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1
  ord : ∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1
  kb : ∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1
  kc : ∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1
  ineL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1
  dist : ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)
  locL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1

structure Two : Prop where
  sq : ∀ g : G T.F Ω, T.rb wPs g ^ 2 = 1
  unr : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.F) A, T.rb wPs g = 1
  atL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := T.F) A, T.rb wPs g = 1
  quad : ∃ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 ∧ IsTotallyReal k₀ ∧
    (∀ p ∈ [2, l], ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ k₀.fixingSubgroup) ∧
    ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ resQ T.F g ∈ k₀.fixingSubgroup
  ord : ∃ n : ℕ, D.ξ ^ 2 ^ n = 1
  xi : ∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker
  bigL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := T.F) A, T.rb wAl g ^ 4 ≠ 1
  big2 : ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → ∃ g ∈ Ine (F := T.F) A, T.rb wAl g ^ 4 ≠ 1

structure Three : Prop where
  five : 5 ≤ l
  sb : D.Sb = ∅
  psi : ∃ m : ℕ, l.Coprime m ∧ D.ψ ^ m = 1
  sq : ∀ g : G T.F Ω, T.rb wPs g = T.rb wAl g ^ 2

structure Three0 (T : Tower D) : Prop where
  five : 5 ≤ l
  sb : D.Sb = ∅
  psi : ∃ m : ℕ, l.Coprime m ∧ D.ψ ^ m = 1

def Fit : Prop := T.Ok ∧ ((Ctx2 D ∧ T.Two) ∨ (Ctx3 D ∧ T.Three0))

def Deep : Prop := ∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, D.ψ (resQ T.F g) ^ m = 1

structure Le (T' : Tower D) : Prop where
  pr : T'.pr = T.pr
  K : T'.K = T.K
  le : T.F ≤ T'.F
  pow : ∃ j : ℕ, ∀ g ∈ T.F.fixingSubgroup, g ^ l ^ j ∈ T'.F.fixingSubgroup
  g0 : ∃ j : ℕ, resQ T'.F T'.g0 = resQ T.F T.g0 ^ l ^ j

abbrev OverQ {R : Type} [CommRing R] (P : PD Unit (G ℚ Ω) R) (P' : PD T.ι (G T.F Ω) R) : Prop :=
  Over (resQ T.F) (fun _ => D.pl l) T.pl P P'

abbrev OverT {T' : Tower D} (h : T.Le T') {R : Type} [CommRing R] (P : PD T.ι (G T.F Ω) R) (P' : PD T'.ι (G T'.F Ω) R) : Prop :=
  Over (resLe h.le) T.pl T'.pl P P'

def Wts (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

end Tower

end UpperTheory.V.Ws

end

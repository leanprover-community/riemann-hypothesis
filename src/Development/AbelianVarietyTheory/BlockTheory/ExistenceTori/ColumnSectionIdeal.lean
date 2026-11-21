import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

abbrev MulIso (L : LB A.left) (N : ℕ) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])

abbrev FrameAt (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))

theorem comp_mulA {T : Over S} (x : T ⟶ A) (N : ℕ) : x ≫ mulA A N = x ^ N := by
  induction N with
  | zero => simp [mulA, MonObj.comp_one]
  | succ n ih =>
    have ih' : x ≫ 𝟙 A ^ n = x ^ n := ih
    simp only [mulA, pow_succ, MonObj.comp_mul, ih', Category.comp_id]

theorem mulIsoT_le (L : LB A.left) (N : ℕ) (T : Over S) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, (snd T A ^ N).left] j ≤
      (snd T A).left ⁻¹ᵁ LB.wchart L ![𝟙 A.left, (mulA A N).left] j := by
  intro y hy
  have h0 : (snd T A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have h1 : (snd T A ^ N).left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : (snd T A).left ≫ (mulA A N).left = (snd T A ^ N).left := by
    rw [← Over.comp_left, comp_mulA]
  rw [← e] at h1
  refine Set.mem_iInter.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1

def mulIsoT (L : LB A.left) (N : ℕ) (α : MulIso A L N) (T : Over S) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]) where
  s := fun j => res (mulIsoT_le A L N T j) (pullU (snd T A).left _ (α.s j))

theorem one_left (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem originFrame_le (L : LB A.left) (T : Over S) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j ≤
      LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) j :=
  le_of_eq (by rw [one_left])

def originFrame (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (T : Over S) :
    FrameAt A L k (1 : T ⟶ A) where
  s := fun j => res (originFrame_le A L T j) ((rigT A L rig T k).s j)

def pullFrame (L : LB A.left) (k : ℤ) {T T' : Over S} (π : T' ⟶ T) (x : T ⟶ A)
    (τ : FrameAt A L k x) : FrameAt A L k (π ≫ x) :=
  LB.pullGen L _ _ τ π.left

def IsOddSymLift (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) (U : ThetaGrp A L k T) : Prop :=
  ∃ M : ℕ, Odd M ∧ x ^ M = 1 ∧ SymLift A L k M x U

def IsRigMulIso (L : RigLB A) (N : ℕ) (α : MulIso A L.L N) : Prop :=
  α.IsGen ∧ IsNormMul A L.L L.rig N α

def IsActMulPull (L : LB A.left) (N : ℕ) (α : MulIso A L N) {T : Over S}
    (U : ThetaGrp A L ((N : ℤ) ^ 2) T) (s : LB.Sec (LPow A L 1 T))
    (F : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T),
    IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 (mulIsoT A L N α T) s s₁ ∧
    IsActOf A L ((N : ℤ) ^ 2) U s₁ F

def IsActMulFrame (L : RigLB A) (N : ℕ) (α : MulIso A L.L N) {T : Over S}
    (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T) (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  U.pt ^ N = t ∧ τ.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _
        (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ U.φ (ptSecT A 1).left)
          (LB.pullGen L.L _ _ α U.pt.left)) τ)
      (rigT A L.L L.rig T ((N : ℤ) ^ 2))

def IsTranslPullAt [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over S} (t t' : T ⟶ A)
    (s : LB.Sec (LPow A L.L 1 T)) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ t' ^ N = t ∧
    ∃ (α : MulIso A L.L N) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
      IsRigMulIso A L N α ∧ IsOddSymLift A L.L ((N : ℤ) ^ 2) t' U ∧ IsActMulPull A L.L N α U s F

def IsTranslFrameAt [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over S} (t t' : T ⟶ A)
    (τ : FrameAt A L.L 1 t) : Prop :=
  Odd N ∧ t' ^ N = t ∧
    ∃ (α : MulIso A L.L N) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
      IsRigMulIso A L N α ∧ IsOddSymLift A L.L ((N : ℤ) ^ 2) t' U ∧ IsActMulFrame A L N α U t τ

def IsTranslPullOver [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ t' : T ⟶ A, C T t' ∧ IsTranslPullAt A L N t t' s F

def IsTranslFrameOver [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  ∃ t' : T ⟶ A, C T t' ∧ IsTranslFrameAt A L N t t' τ

def IsTranslPull [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ ∀ p : T.left, ∃ (T' : Over S) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
    ∃ (s' : LB.Sec (LPow A L.L 1 T')) (F' : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T')),
      IsPullSec A L.L 1 (π ▷ A) (whiskerRight_snd _ _) s s' ∧
      IsPullSec A L.L ((N : ℤ) ^ 2) (π ▷ A) (whiskerRight_snd _ _) F F' ∧
      IsTranslPullOver A L N C (π ≫ t) s' F'

def IsTranslFrame [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  Odd N ∧ τ.IsGen ∧
    ∀ p : T.left, ∃ (T' : Over S) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
      IsTranslFrameOver A L N C (π ≫ t) (pullFrame A L.L 1 π t τ)

def ValueNamedSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  ∀ (N : ℕ) (α : MulIso A L.L N), α.IsGen → ∀ {T : Over S} (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T)
    (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T)) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T))
    (τ : FrameAt A L.L 1 t), IsActMulPull A L.L N α U s F → IsActMulFrame A L N α U t τ →
    ∀ v : Γ(T.left, ⊤),
      IsValueAt A L.L ((N : ℤ) ^ 2) F 1 (originFrame A L.L L.rig ((N : ℤ) ^ 2) T) v ↔
        IsValueAt A L.L 1 s t τ v

def ValueSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → ∀ (N : ℕ) {T : Over S} (t t' : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (τ : FrameAt A L.L 1 t),
    IsTranslPullAt A L N t t' s F → IsTranslFrameAt A L N t t' τ →
    ∀ v : Γ(T.left, ⊤),
      IsValueAt A L.L ((N : ℤ) ^ 2) F 1 (originFrame A L.L L.rig ((N : ℤ) ^ 2) T) v ↔
        IsValueAt A L.L 1 s t τ v

def OddSymLiftSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (k : ℤ) {T : Over S} (x : T ⟶ A) (M : ℕ), Odd M → x ^ M = 1 →
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L.L k (overRes V), θ.pt = overResι V ≫ x) →
    ∃ U : ThetaGrp A L.L k T, SymLift A L.L k M x U ∧
      ∀ U' : ThetaGrp A L.L k T, IsOddSymLift A L.L k x U' → U' = U

def DescentFixSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (N : ℕ) (α : MulIso A L.L N), IsRigMulIso A L N α →
    ∀ {T : Over S} (x : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
      (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)), Odd N → x ^ N = 1 →
      IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1
        (mulIsoT A L.L N α T) s s₁ →
      IsTranslPullAt A L N 1 x s s₁

def FreeOfDivisionSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (N : ℕ) {T : Over S} (t t₁ t₂ : T ⟶ A),
    WeilIs A L.L ((N : ℤ) ^ 2) t₁ t₂ 1 →
    (∀ (s : LB.Sec (LPow A L.L 1 T)) (F₁ F₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)),
      IsTranslPullAt A L N t t₁ s F₁ → IsTranslPullAt A L N t t₂ s F₂ → F₁ = F₂) ∧
    ∀ τ₁ τ₂ : FrameAt A L.L 1 t,
      IsTranslFrameAt A L N t t₁ τ₁ → IsTranslFrameAt A L N t t₂ τ₂ → τ₁ = τ₂

end GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Row (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

abbrev Pol (Dw : Datum H) {l : Level H} (c : Coeff l) (n : ℕ) : Type :=
  MvPolynomial (Letter (E →+* ℂ) Dw.mult n) c.F

def colExp {Dw : Datum H} {n : ℕ} (m : Letter (E →+* ℂ) Dw.mult n →₀ ℕ) (j : Fin n) : Row Dw → ℕ :=
  fun ρ => m ⟨ρ.1, ρ.2, j⟩

def intRing {l : Level H} (c : Coeff l) : Subring c.F := (algebraMap (𝓞 c.F) c.F).range

def HHset (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Pol Dw c n) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (fun τ => τ (H.rt : E) = H.rt0) (fun τ i => a (τ, i))

def Hset (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Pol Dw c n) :=
  HaO Dw.mult n c.F (intRing c) ComplexEmbedding.conjugate (fun τ => τ (H.rt : E) = H.rt0) (fun τ i => a (τ, i))

def HLat (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Submodule (𝓞 c.F) (Pol Dw c n) where
  carrier := Hset Dw c a n
  zero_mem' := ⟨⟨Submodule.zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩,
    fun _ => by simp⟩
  add_mem' := by
    classical
    rintro P Q ⟨⟨hP1, hP2, hP3⟩, hP4⟩ ⟨⟨hQ1, hQ2, hQ3⟩, hQ4⟩
    refine ⟨⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_add, hP2 σ i i' h t, hQ2 σ i i' h t]
    · rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hP3 m h
      · exact hQ3 m h
    · rw [MvPolynomial.coeff_add]; exact Subring.add_mem _ (hP4 m) (hQ4 m)
  smul_mem' := by
    rintro r P ⟨⟨hP1, hP2, hP3⟩, hP4⟩
    have e : r • P = (algebraMap (𝓞 c.F) c.F r) • P := (algebraMap_smul _ r P).symm
    suffices hs : (algebraMap (𝓞 c.F) c.F r) • P ∈ Hset Dw c a n from
      (congrArg (fun Q => Q ∈ Hset Dw c a n) e).mpr hs
    refine ⟨⟨Submodule.smul_mem _ _ hP1, fun σ i i' h t => ?_, fun m hm => ?_⟩, fun m => ?_⟩
    · rw [map_smul, hP2 σ i i' h t]
    · exact hP3 m (MvPolynomial.support_smul hm)
    · rw [MvPolynomial.coeff_smul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hP4 m)

def admitted (l : Level H) (N : ℕ) : Prop := Odd N ∧ l.M ∣ N

open Classical in

def transIdeal (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ∏ 𝔓 ∈ (UniqueFactorizationMonoid.normalizedFactors l.Mb).toFinset,
    𝔓 ^ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 E)})).count 𝔓

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def KilledBy (I : Ideal (𝓞 E)) (T : Over Xo.X) (z : T ⟶ Xo.univ.t.G) : Prop :=
  ∀ b ∈ I, z ≫ Xo.univ.t.act.act b = 1

def levelPt (T : Over Xo.X) (x : Dw.La) : T ⟶ Xo.univ.t.G := toUnit T ≫ Xo.univ.eta x

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ) : Type :=
  LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk y.x))

abbrev Jet : Type 1 :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ), SecAt Xo c y k → (Row Dw → ℕ) → S

variable {Xo c}

def pairBox (J : Jet Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ) {n : ℕ}
    (P : Pol Dw c n) (F : Fin n → SecAt Xo c y k) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ j, J S y k (F j) (colExp m j)

def IsColSec (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (x : Dw.La)
    (F : SecAt Xo c y ((N : ℤ) ^ 2)) : Prop :=
  TranslationFrames.IsTranslPull Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo (transIdeal l N ^ 2))
    (levelPt Xo (Over.mk y.x) x) y.s F

def IsThValueAt (J : Jet Xo c) (N : ℕ) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  admitted l N ∧ ∃ F : Fin n → SecAt Xo c y ((N : ℤ) ^ 2), (∀ j, IsColSec N y (x j) (F j)) ∧
    v = algebraMap c.F S (((N : c.F)⁻¹) ^ P.totalDegree) * pairBox J y ((N : ℤ) ^ 2) P F

def IsThValue (J : Jet Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  IsThValueAt J l.M x P y v

def IsThRule (J : Jet Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : Pol Dw c n) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsThValue J x P y (f p y)

def IsTh (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : Pol Dw c n)
    (f : Rul Xo c) : Prop :=
  P ∈ Hset Dw c a n ∧ IsThRule J x P f

def thGenOn (J : Jet Xo c) {n : ℕ} (B : Set (Pol Dw c n)) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La), ∃ P ∈ B, IsThRule J x P f}

def thGen (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La) (P : Pol Dw c n), IsTh J a n x P f}

def thAll (J : Jet Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  Submodule.span (𝓞 c.F) (thGen J a n)

def LatticeSt (Dw : Datum H) (c : Coeff l) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (HLat Dw c a n).FG ∧
    (Submodule.span c.F (Hset Dw c a n) : Set (Pol Dw c n)) = HHset Dw c a n

def TransIdealSt (Xo : Moduli Dw l) : Prop :=
  transIdeal l l.M = l.Mb ∧ ∀ N, admitted l N → ∀ (T : Over Xo.X) (x : Dw.La),
    KilledBy Xo (transIdeal l N) T (levelPt Xo T x)

def ColSecSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ N, admitted l N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (x : Dw.La),
    ∃! F, IsColSec N y x F

def FreeOfNSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n, ∀ N N', admitted l N → admitted l N' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      IsThValueAt J N x P y v ↔ IsThValueAt J N' x P y v

def BaseChangeSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n,
    ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (z : FrPt Xo c T) (v : S), FrMap φ y z → IsThValue J x P y v → IsThValue J x P z (φ v)

def RationalSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La), ∀ P ∈ Hset Dw c a n,
    (∃! f, IsTh J a n x P f) ∧ ∀ f, IsTh J a n x P f → f ∈ sec Xo c a n

def BasisSpanSt (J : Jet Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (B : Set (Pol Dw c n)),
    (AddSubgroup.closure B : Set (Pol Dw c n)) = Hset Dw c a n →
    Submodule.span (𝓞 c.F) (thGenOn J B) = thAll J a n

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnSectionIdeal
end
end

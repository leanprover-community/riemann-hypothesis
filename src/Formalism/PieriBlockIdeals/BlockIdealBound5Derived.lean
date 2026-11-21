import Mathlib
import Formalism.RankGapBounds.TheoremALocOfLemmaA
import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.FactorialValuationSum
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.PieriBlockIdeals.LemmaWAssembled

section
noncomputable section

open TensorProduct

namespace Formalism.CohomologicalDescent.AutomorphicFormLattices

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization

def TensorProductLattices : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) [∀ i, Module.Free k (B i)] (l : k)
    (e : ι → ℕ), l ∈ nonZeroDivisors k → (∀ i, LatIncl l (B i) (e i)) →
    Function.Injective (PiTensorProduct.map fun i => (B i).subtype) ∧
      ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B

def ExpBaseChange : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] [Module.FaithfullyFlat k k']
    (A : Type) [AddCommGroup A] [Module k A] (B : Submodule k A) (l : k),
    Function.Injective (B.subtype.baseChange k') ∧
    (∀ J : ℕ, LatIncl (algebraMap k k' l) (LinearMap.range (B.subtype.baseChange k')) J ↔
      LatIncl l B J) ∧
    sInf {J : ℕ | LatIncl (algebraMap k k' l) (LinearMap.range (B.subtype.baseChange k')) J} =
      sInf {J : ℕ | LatIncl l B J}

section Defs

variable {G : Type} [Group G] {k : Type} [CommRing k]

def IsIntertw {H : Type} [Monoid H] {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] (ρ₁ : Representation k H W₁) (ρ₂ : Representation k H W₂)
    (φ : W₁ →ₗ[k] W₂) : Prop :=
  ∀ (κ : H) (w : W₁), φ (ρ₁ κ w) = ρ₂ κ (φ w)

def invMap {H : Type} [Group H] {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] {ρ₁ : Representation k H W₁} {ρ₂ : Representation k H W₂}
    (φ : W₁ →ₗ[k] W₂) (hφ : IsIntertw ρ₁ ρ₂ φ) : ρ₁.invariants →ₗ[k] ρ₂.invariants :=
  φ.restrict (fun w hw κ => by rw [← hφ, hw κ])

def mapM (Γ K : Subgroup G) {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] {ρ₁ : Representation k K W₁} {ρ₂ : Representation k K W₂}
    (φ : W₁ →ₗ[k] W₂) (hφ : IsIntertw ρ₁ ρ₂ φ) : AMFK k Γ K ρ₁ →ₗ[k] AMFK k Γ K ρ₂ :=
  (φ.compLeft G).restrict (fun f hf γ g κ => by
    show φ (f _) = ρ₂ κ⁻¹ (φ (f g))
    rw [hf γ g κ, hφ])

def GamAt (Γ K : Subgroup G) (x : G) : Subgroup G := Γ ⊓ K.map (MulAut.conj x).toMonoidHom

def stabK (Γ K : Subgroup G) (x : G) : Subgroup K :=
  Γ.comap ((MulAut.conj x).toMonoidHom.comp K.subtype)

def resTo {K : Type} [Group K] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (H : Subgroup K) : Representation k H W := MonoidHom.comp ρ H.subtype

def OrdersInvertible (k : Type) [CommRing k] (Γ K : Subgroup G) : Prop :=
  ∀ x : G, Finite (GamAt Γ K x) ∧ IsUnit ((Nat.card (GamAt Γ K x) : ℕ) : k)

theorem isIntertw_subtype {K : Subgroup G} {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (U : Submodule k W) (hU : IsStable ρ U) :
    IsIntertw (resRep ρ U hU) ρ U.subtype := fun _ _ => rfl

theorem isIntertw_rTensor {H : Type} [Monoid H] {W₁ W₂ Θ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] [AddCommGroup Θ] [Module k Θ]
    {ρ₁ : Representation k H W₁} {ρ₂ : Representation k H W₂} (θ : Representation k H Θ)
    {φ : W₁ →ₗ[k] W₂} (hφ : IsIntertw ρ₁ ρ₂ φ) :
    IsIntertw (ρ₁.tprod θ) (ρ₂.tprod θ) (φ.rTensor Θ) := by
  intro κ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [hφ κ a]
  | add a b ha hb => simp only [map_add, ha, hb]

def powSub {W : Type} [AddCommGroup W] [Module k W] (l : k) (c : ℕ) : Submodule k W :=
  LinearMap.range ((l ^ c) • (LinearMap.id : W →ₗ[k] W))

theorem isStable_powSub {K : Subgroup G} {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (l : k) (c : ℕ) : IsStable ρ (powSub (W := W) l c) := by
  rintro κ _ ⟨w, rfl⟩
  exact ⟨ρ κ w, by simp⟩

end Defs

def StabIso : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (x : G),
    ∃ e : GamAt Γ K x ≃* stabK Γ K x, ∀ γ, (((e γ : stabK Γ K x) : K) : G) = x⁻¹ * (γ : G) * x

def AMFKDecomp : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type) [AddCommGroup W]
    [Module k W] (ρ : Representation k K W) (s : ClassSet Γ K → G),
    (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∃ e : AMFK k Γ K ρ ≃ₗ[k] ((c : ClassSet Γ K) → (resTo ρ (stabK Γ K (s c))).invariants),
      ∀ f c, (e f c : W) = (f : G → W) (s c)

def LocIncl : Prop :=
  ∀ (T : Type) [CommRing T] (P' P : Type) [AddCommGroup P'] [Module T P'] [AddCommGroup P]
    [Module T P] (ι : P' →ₗ[T] P) (S : Submonoid T) (t : T) (J : ℕ),
    Function.Injective ι → (∀ x : P, t ^ J • x ∈ LinearMap.range ι) →
    Function.Injective (LocalizedModule.map S ι) ∧
      ∀ y : LocalizedModule S P, t ^ J • y ∈ LinearMap.range (LocalizedModule.map S ι)

def LatticeInclusionFormsInjective : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (B : Type) [AddCommGroup B]
    [Module k B] (ρ : Representation k K B) (A : Submodule k B) (hA : IsStable ρ A) (l : k) (J : ℕ),
    LatIncl l A J →
    (Function.Injective (mapM Γ K A.subtype (isIntertw_subtype ρ A hA)) ∧
      ∀ f : AMFK k Γ K ρ,
        l ^ J • f ∈ LinearMap.range (mapM Γ K A.subtype (isIntertw_subtype ρ A hA))) ∧
    ∀ (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K (resRep ρ A hA))]
      [Module T (AMFK k Γ K ρ)] [IsScalarTower k T (AMFK k Γ K ρ)]
      (ιT : AMFK k Γ K (resRep ρ A hA) →ₗ[T] AMFK k Γ K ρ) (S : Submonoid T),
      (∀ f, ιT f = mapM Γ K A.subtype (isIntertw_subtype ρ A hA) f) →
      Function.Injective (LocalizedModule.map S ιT) ∧
        ∀ y : LocalizedModule S (AMFK k Γ K ρ),
          (algebraMap k T l) ^ J • y ∈ LinearMap.range (LocalizedModule.map S ιT)

def TensorFreeModuleTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (B : Type) [AddCommGroup B]
    [Module k B] (ρ : Representation k K B) (Θ : Type) [AddCommGroup Θ] [Module k Θ]
    [Module.Free k Θ] (θ : Representation k K Θ) (A : Submodule k B) (hA : IsStable ρ A) (l : k)
    (J : ℕ), LatIncl l A J →
    (Function.Injective (A.subtype.rTensor Θ) ∧
      Function.Injective
        (mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA))) ∧
      ∀ f : AMFK k Γ K (ρ.tprod θ), l ^ J • f ∈ LinearMap.range
        (mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ((resRep ρ A hA).tprod θ))]
      [Module T (AMFK k Γ K (ρ.tprod θ))] [IsScalarTower k T (AMFK k Γ K (ρ.tprod θ))]
      (ιT : AMFK k Γ K ((resRep ρ A hA).tprod θ) →ₗ[T] AMFK k Γ K (ρ.tprod θ)) (S : Submonoid T),
      (∀ f, ιT f =
        mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA)) f) →
      Function.Injective (LocalizedModule.map S ιT) ∧
        ∀ y : LocalizedModule S (AMFK k Γ K (ρ.tprod θ)),
          (algebraMap k T l) ^ J • y ∈ LinearMap.range (LocalizedModule.map S ιT)

def OrderBound : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L)
    (g : Matrix (Fin N) (Fin N) E), l.Prime → IsPrimitiveRoot ζ l →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 → g ^ l = 1 → g ≠ 1 → l - 1 ≤ N

def NoOrderL : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L)
    (Δ : Subgroup (GL (Fin N) E)), l.Prime → IsPrimitiveRoot ζ l →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 → Finite Δ → N + 1 < l →
    ¬ l ∣ Nat.card Δ

def CardUnit : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l n : ℕ), l.Prime →
    (l : O) ∈ IsLocalRing.maximalIdeal O → ¬ l ∣ n → IsUnit (n : O)

def InvExact : Prop :=
  ∀ (k : Type) [CommRing k] (H : Type) [Group H] [Finite H] (A B C : Type) [AddCommGroup A]
    [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k H A) (ρB : Representation k H B) (ρC : Representation k H C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    IsUnit ((Nat.card H : ℕ) : k) → Function.Exact f g → Function.Exact (invMap f hf) (invMap g hg)

def MLeftExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    Function.Injective f → Function.Exact f g →
    Function.Injective (mapM Γ K f hf) ∧ Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)

def MExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    OrdersInvertible k Γ K → Function.Exact f g →
    Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)

def MTExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (Θ : Type) [AddCommGroup Θ] [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    OrdersInvertible k Γ K → Function.Exact f g →
    Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
      (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg))

def PointsLemmaAnyRank : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L) (G : Type) [Group G]
    (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 →
    N + 1 < l → Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    (∀ x : G, ¬ l ∣ Nat.card (GamAt Γ K x)) ∧
    ∀ (A B C : Type) [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C]
      [Module O C] (ρA : Representation O K A) (ρB : Representation O K B)
      (ρC : Representation O K C) (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : IsIntertw ρA ρB f)
      (hg : IsIntertw ρB ρC g), Function.Exact f g →
      Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)

def FormsExactTypes : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L) (G : Type) [Group G]
    (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 →
    N + 1 < l → Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    ∀ (A B C : Type) [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C]
      [Module O C] (ρA : Representation O K A) (ρB : Representation O K B)
      (ρC : Representation O K C) (Θ : Type) [AddCommGroup Θ] [Module O Θ] [Module.Free O Θ]
      (θ : Representation O K Θ) (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : IsIntertw ρA ρB f)
      (hg : IsIntertw ρB ρC g), Function.Exact f g →
      Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
        (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg))

def ShortExactFormsExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B Q : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup Q] [Module k Q]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρQ : Representation k K Q)
    (f : A →ₗ[k] B) (g : B →ₗ[k] Q) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρQ g),
    OrdersInvertible k Γ K → Function.Injective f → Function.Exact f g → Function.Surjective g →
    Function.Injective (mapM Γ K f hf) ∧ Function.Exact (mapM Γ K f hf) (mapM Γ K g hg) ∧
    Function.Surjective (mapM Γ K g hg) ∧
    ∃ e : (AMFK k Γ K ρB ⧸ LinearMap.range (mapM Γ K f hf)) ≃ₗ[k] AMFK k Γ K ρQ,
      ∀ φ, e (Submodule.Quotient.mk φ) = mapM Γ K g hg φ

def PowerScaledFormsEq : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (Q : Type)
    [AddCommGroup Q] [Module k Q] (ρ : Representation k K Q) (l : k) (c : ℕ),
    OrdersInvertible k Γ K →
    ∀ φ : G → Q, φ ∈ formsIn Γ K ρ (powSub l c) ↔ ∃ ψ ∈ AMFK k Γ K ρ, φ = l ^ c • ψ

def FiltrationFormsGraded : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (n : ℕ) (F Gr : ℕ → Type)
    [∀ j, AddCommGroup (F j)] [∀ j, Module k (F j)] [∀ j, AddCommGroup (Gr j)]
    [∀ j, Module k (Gr j)] (ρF : ∀ j, Representation k K (F j))
    (ρG : ∀ j, Representation k K (Gr j)) (i : ∀ j, F j →ₗ[k] F (j + 1))
    (p : ∀ j, F (j + 1) →ₗ[k] Gr j) (hi : ∀ j, IsIntertw (ρF j) (ρF (j + 1)) (i j))
    (hp : ∀ j, IsIntertw (ρF (j + 1)) (ρG j) (p j)) (T : Type) [CommRing T]
    [∀ j, Module T (AMFK k Γ K (ρF j))] [∀ j, Module T (AMFK k Γ K (ρG j))] (S : Submonoid T),
    Subsingleton (F 0) → (∀ j < n, Function.Injective (i j)) →
    (∀ j < n, Function.Exact (i j) (p j)) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K (ρF j)),
      mapM Γ K (i j) (hi j) (t • φ) = t • mapM Γ K (i j) (hi j) φ) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K (ρF (j + 1))),
      mapM Γ K (p j) (hp j) (t • φ) = t • mapM Γ K (p j) (hp j) φ) →
    (∀ j < n, Subsingleton (LocalizedModule S (AMFK k Γ K (ρG j)))) →
    Subsingleton (LocalizedModule S (AMFK k Γ K (ρF n)))

def ShortExactFormsExactTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B Q : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup Q] [Module k Q]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρQ : Representation k K Q)
    (Θ : Type) [AddCommGroup Θ] [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ)
    (f : A →ₗ[k] B) (g : B →ₗ[k] Q) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρQ g),
    OrdersInvertible k Γ K → Function.Injective f → Function.Exact f g → Function.Surjective g →
    Function.Injective (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf)) ∧
    Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
      (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg)) ∧
    Function.Surjective (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg)) ∧
    ∃ e : (AMFK k Γ K (ρB.tprod θ) ⧸
        LinearMap.range (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))) ≃ₗ[k]
          AMFK k Γ K (ρQ.tprod θ),
      ∀ φ, e (Submodule.Quotient.mk φ) = mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg) φ

def PowerScaledFormsTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (Q : Type)
    [AddCommGroup Q] [Module k Q] (ρ : Representation k K Q) (Θ : Type) [AddCommGroup Θ]
    [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ) (l : k) (c : ℕ),
    OrdersInvertible k Γ K →
    Function.Injective (mapM Γ K ((powSub (W := Q) l c).subtype.rTensor Θ)
      (isIntertw_rTensor θ (isIntertw_subtype ρ _ (isStable_powSub ρ l c)))) ∧
    ∀ φ : AMFK k Γ K (ρ.tprod θ),
      φ ∈ LinearMap.range (mapM Γ K ((powSub (W := Q) l c).subtype.rTensor Θ)
        (isIntertw_rTensor θ (isIntertw_subtype ρ _ (isStable_powSub ρ l c)))) ↔
      ∃ ψ : AMFK k Γ K (ρ.tprod θ), φ = l ^ c • ψ

def FiltrationFormsGradedTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (n : ℕ) (F Gr : ℕ → Type)
    [∀ j, AddCommGroup (F j)] [∀ j, Module k (F j)] [∀ j, AddCommGroup (Gr j)]
    [∀ j, Module k (Gr j)] (ρF : ∀ j, Representation k K (F j))
    (ρG : ∀ j, Representation k K (Gr j)) (Θ : Type) [AddCommGroup Θ] [Module k Θ]
    [Module.Free k Θ] (θ : Representation k K Θ) (i : ∀ j, F j →ₗ[k] F (j + 1))
    (p : ∀ j, F (j + 1) →ₗ[k] Gr j) (hi : ∀ j, IsIntertw (ρF j) (ρF (j + 1)) (i j))
    (hp : ∀ j, IsIntertw (ρF (j + 1)) (ρG j) (p j)) (T : Type) [CommRing T]
    [∀ j, Module T (AMFK k Γ K ((ρF j).tprod θ))] [∀ j, Module T (AMFK k Γ K ((ρG j).tprod θ))]
    (S : Submonoid T),
    Subsingleton (F 0) → (∀ j < n, Function.Injective (i j)) →
    (∀ j < n, Function.Exact (i j) (p j)) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K ((ρF j).tprod θ)),
      mapM Γ K ((i j).rTensor Θ) (isIntertw_rTensor θ (hi j)) (t • φ) =
        t • mapM Γ K ((i j).rTensor Θ) (isIntertw_rTensor θ (hi j)) φ) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K ((ρF (j + 1)).tprod θ)),
      mapM Γ K ((p j).rTensor Θ) (isIntertw_rTensor θ (hp j)) (t • φ) =
        t • mapM Γ K ((p j).rTensor Θ) (isIntertw_rTensor θ (hp j)) φ) →
    (∀ j < n, Subsingleton (LocalizedModule S (AMFK k Γ K ((ρG j).tprod θ)))) →
    Subsingleton (LocalizedModule S (AMFK k Γ K ((ρF n).tprod θ)))

def cut {O F V : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module O V]
    [Module F V] [IsScalarTower O F V] (L : Submodule O V) (Z : Submodule F V) : Submodule O V :=
  L ⊓ Z.restrictScalars O

def DVRLatticeIntersection : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (Z : Submodule F V) (l : O) (J : ℕ),
    L.FG → l ≠ 0 → (∀ x ∈ L, l ^ J • x ∈ L') →
    (∀ x ∈ cut L Z, l ^ J • x ∈ cut L' Z) ∧
    Module.length O (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
      (J : ℕ∞) * IsDiscreteValuationRing.addVal O l * (Module.finrank O (cut L Z) : ℕ∞) ∧
    (Finite (O ⧸ Ideal.span {l ^ J}) →
      Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
        Nat.card (O ⧸ Ideal.span {l ^ J}) ^ Module.finrank O (cut L Z))

def LatticeIntersectionRank : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L : Submodule O V) (Z : Submodule F V), L.FG →
    Module.finrank O (cut L Z) = Module.finrank F ↥(Submodule.span F (L : Set V) ⊓ Z) ∧
    (Module.Finite F Z → Module.finrank O (cut L Z) ≤ Module.finrank F Z)

def CardQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (J : ℕ),
    Nat.card (O ⧸ Ideal.span {(l : O) ^ J}) = l ^ (J * Module.finrank ℤ_[l] O)

def LatticeIntersectionIndexCost : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (Z : Submodule F V) (J : ℕ),
    L.FG → (∀ x ∈ L, (l : O) ^ J • x ∈ L') →
    Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
      l ^ (J * Module.finrank ℤ_[l] O * Module.finrank O (cut L Z)) ∧
    Real.log (Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype)) /
        (Module.finrank ℤ_[l] O : ℝ) ≤
      (J : ℝ) * (Module.finrank O (cut L Z) : ℝ) * Real.log l

def Translate : Prop :=
  ∀ (N h m : ℤ) (H Hc : Multiset ℤ), Hc = H.map (fun x => N - 1 - x) → m ∈ H →
    (∀ x ∈ H, m ≤ x) → (∀ x ∈ H, x ≤ m + h) →
    (∀ u ∈ H.map (fun x => x + -m), 0 ≤ u ∧ u ≤ h) ∧ (0 : ℤ) ∈ H.map (fun x => x + -m) ∧
    Hc.map (fun x => x + (h - N + 1 - -m)) = (H.map (fun x => x + -m)).map (fun u => h - u) ∧
    (∀ u ∈ Hc.map (fun x => x + (h - N + 1 - -m)), 0 ≤ u ∧ u ≤ h) ∧
    -m + (h - N + 1 - -m) = h - N + 1

def TranslateInv : Prop :=
  (∀ (l : ℕ) (b c : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (b + c) t κ (U.image (fun u => u + c)) = mwCount l b t κ U) ∧
  ∀ (n r : ℕ) (U U' : Fin n → ℤ) (c : ℤ),
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => (a : ℕ) < r), ((U a + c) - (U' a + c)) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => (a : ℕ) < r), (U a - U' a)

def TypeOnReal : Prop :=
  ∀ (M : Type) [CommGroup M] (ι : Type) (Φ : Finset ι) (a : ι → M) (c c' : ι → ℤ) (w₀ : ℤ),
    (∀ τ ∈ Φ, c τ + c' τ = w₀) →
    ∏ τ ∈ Φ, (a τ ^ c τ * a τ ^ c' τ) = (∏ τ ∈ Φ, a τ) ^ w₀

def RootSep : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (𝔮 : Ideal R) (M : ℕ) (z : R), 𝔮.IsPrime →
    (M : R) ∉ 𝔮 → z ^ M = 1 → z - 1 ∈ 𝔮 → z = 1

def CharExt : Prop :=
  ∀ (I : Type) [CommGroup I] (P : Subgroup I) (χ : P →* ℂˣ),
    ∃ χ' : I →* ℂˣ, ∀ x : P, χ' (x : I) = χ x

def ExpExists : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (l : O), L.FG → l ∈ IsLocalRing.maximalIdeal O →
    (L : Set V) ⊆ Submodule.span F (L' : Set V) → ∃ J : ℕ, ∀ x ∈ L, l ^ J • x ∈ L'

def DegreeOfInf : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l : ℕ) (ζ : L), l.Prime →
    IsPrimitiveRoot ζ l → E ⊓ IntermediateField.adjoin ℚ {ζ} = ⊥ →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1

def DegreeOfDiscr : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l : ℕ) (ζ : L), l.Prime →
    IsPrimitiveRoot ζ l → ¬ (l : ℤ) ∣ NumberField.discr E →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1

def NumberFieldOrdersPrime : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l N : ℕ) (ζ : L) (G : Type)
    [Group G] (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → ¬ (l : ℤ) ∣ NumberField.discr E → N + 1 < l →
    Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    (∀ x : G, ¬ l ∣ Nat.card (GamAt Γ K x)) ∧ OrdersInvertible O Γ K

def TypeCong : Prop :=
  ∀ (R : Type) [CommRing R] (𝔮 : Ideal R) (ι : Type) (Φ : Finset ι) (a : ι → Rˣ) (c : ι → ℤ),
    (∀ τ ∈ Φ, (a τ : R) - 1 ∈ 𝔮) → ((∏ τ ∈ Φ, a τ ^ c τ : Rˣ) : R) - 1 ∈ 𝔮

def TypeTrivialOnUnits : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (𝔮 : Ideal R) (M : ℕ) (ι : Type) (Φ : Finset ι)
    (a : ι → Rˣ) (c : ι → ℤ), 𝔮.IsPrime → (M : R) ∉ 𝔮 → (∀ τ ∈ Φ, (a τ : R) - 1 ∈ 𝔮) →
    (∏ τ ∈ Φ, a τ ^ c τ) ^ M = 1 → ∏ τ ∈ Φ, a τ ^ c τ = 1

def CharOfType : Prop :=
  ∀ (E₁ I : Type) [CommGroup E₁] [CommGroup I] (ι : E₁ →* I) (Ty : E₁ →* ℂˣ),
    (∀ u, ι u = 1 → Ty u = 1) → ∃ χ : I →* ℂˣ, ∀ α, χ (ι α) = Ty α

def HeckeFunct : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (k : Type) [CommRing k]
    (W₁ W₂ : Type) [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    (φ : W₁ →ₗ[k] W₂) (f : G₁ → k) (ψ : G₁ × G₂ → W₁), IsCommensurated K₁ → f ∈ Hecke k K₁ →
    ∀ g, hActK K₁ f (fun x => φ (ψ x)) g = φ (hActK K₁ f ψ g)

end Formalism.CohomologicalDescent.AutomorphicFormLattices
end
end

section
noncomputable section

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

def nablaWtR (R : Type) [CommRing R] (r : ℕ) (ν μ : Fin r → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin r) R) :=
  dualWeyl R r r ν ⊓ weightedHomogeneousSubmodule R (rowW r r) μ

def ExpLeRing : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ),
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → ExpLe l r ν μ e →
    ∀ x ∈ nablaWtR R r ν μ, (l : R) ^ e • x ∈ weyl R r r le_rfl ν

def ExpLeRingComp : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ),
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → ExpLe l r ν μ e →
    ∀ x ∈ dualWeyl R r r ν, weightedHomogeneousComponent (rowW r r) μ x ∈ dualWeyl R r r ν ∧
      (l : R) ^ e • weightedHomogeneousComponent (rowW r r) μ x ∈ weyl R r r le_rfl ν

def DepthNonneg : Prop :=
  ∀ (r c : ℕ) (ν μ : Fin r → ℕ), Antitone ν → nablaWt r ν μ ≠ ⊥ →
    ∑ a, μ a = ∑ a, ν a ∧ 0 ≤ depth2 (res r (varpi c)) ν μ

def ApplicationWindow : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    (∀ a, a < k → xm ≤ UN (k + j + t + q) lam a ∧ UN (k + j + t + q) lam a ≤ xp) →
    (∀ a, k ≤ a → a < k + j → UN (k + j + t + q) lam a < xm) →
    UN (k + j + t + q) lam (k + j) < xm → xm ≤ xp → xp - UN (k + j + t + q) lam (k + j) ≤ (h : ℤ) →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl xm xp (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊

def chainB {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) : ∀ τ, Submodule O (Nb τ) :=
  fun τ => if τ ∈ s then ⊤ else B τ

def atFactor {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) : (⨂[O] τ, Nb τ) →ₗ[O] (⨂[O] τ, Nb τ) :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) τ p)

def AtFactorTprod : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) (x : ∀ τ, Nb τ),
    atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ)))

def TensorWeightKill : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) (a : ι)
    (p : Nb a →ₗ[O] Nb a) (l : O) (c : ℕ), a ∉ s → (∀ x, l ^ c • p x ∈ B a) →
    ∀ y ∈ tensSub (chainB B (insert a s)), l ^ c • atFactor a p y ∈ tensSub (chainB B s)

def ChainEnds : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)),
    tensSub (chainB B ∅) = tensSub B ∧ tensSub (chainB B Finset.univ) = ⊤

def ChainMono : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s s' : Finset ι),
    s ⊆ s' → tensSub (chainB B s) ≤ tensSub (chainB B s')

def TensorProjKill : Prop :=
  ∀ (R : Type) [CommRing R] (P X P' : Type) [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    [AddCommGroup P'] [Module R P'] (p : X →ₗ[R] X) (l : R) (c : ℕ), (∀ x : X, l ^ c • p x = 0) →
    ∀ z : P ⊗[R] (X ⊗[R] P'),
      l ^ c • TensorProduct.map LinearMap.id (TensorProduct.map p LinearMap.id) z = 0

def scaleSub {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : Submodule A V where
  carrier := {x | ∃ y : V, x = c • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, by rw [smul_add]⟩
  smul_mem' := by rintro a _ ⟨y, rfl⟩; exact ⟨a • y, by rw [smul_comm]⟩

def IsSubquot (A : Type) [Ring A] (V G : Type) [AddCommGroup V] [Module A V] [AddCommGroup G]
    [Module A G] : Prop :=
  ∃ (E : Submodule A V) (ψ : E →ₗ[A] G), Function.Surjective ψ

def PowQuotient : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (ϖ : O) (a : ℕ),
    ∃ φ : (V ⧸ scaleSub A V ϖ) →ₗ[A]
        (scaleSub A V (ϖ ^ a) ⧸ (scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype),
      (∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk ⟨ϖ ^ a • v, v, rfl⟩) ∧
      Function.Surjective φ ∧ ((∀ v : V, ϖ • v = 0 → v = 0) → Function.Injective φ)

def SimpleSubquotOfPower : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (ϖ : O) (n : ℕ) (F F' : Submodule A V),
    F ≤ F' → scaleSub A V (ϖ ^ n) ≤ F → IsSimpleModule A (F' ⧸ F.comap F'.subtype) →
    IsSubquot A (V ⧸ scaleSub A V ϖ) (F' ⧸ F.comap F'.subtype)

def SubquotIso : Prop :=
  ∀ (A : Type) [Ring A] (V G G' : Type) [AddCommGroup V] [Module A V] [AddCommGroup G] [Module A G]
    [AddCommGroup G'] [Module A G'], Nonempty (G ≃ₗ[A] G') → IsSubquot A V G → IsSubquot A V G'

def repOf (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] : Representation O K W :=
  ((Algebra.lsmul O O W : A →ₐ[O] Module.End O W) : A →* Module.End O W).comp jK

abbrev Forms (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] : Submodule O (G → W) :=
  AMFK O Γ K (repOf O jK W)

def RepOfApply : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (K : Subgroup G)
    (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W]
    (κ : K) (w : W), repOf O jK W κ w = jK κ • w

def HeckeStable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [Module T (Forms O Γ jK V)] :
    Prop :=
  ∀ (U : Submodule A V) (t : T) (f : Forms O Γ jK V), (∀ g, (f : G → V) g ∈ U) →
    ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U

def HeckeNat (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V W : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] :
    Prop :=
  ∀ (U : Submodule A V) (ψ : U →ₗ[A] W) (t : T) (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
    (hf : ∀ g, (f : G → V) g ∈ U) (hf' : ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
    (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
    ∀ g, ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨((t • f : Forms O Γ jK V) : G → V) g, hf' g⟩

def FormsStep : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W]
    [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] (S : Submonoid T)
    (F F' : Submodule A V) (ψ : F' →ₗ[A] W),
    HeckeStable O Γ jK T V → HeckeNat O Γ jK T V W → (∀ x : F', ψ x = 0 → (x : V) ∈ F) →
    Subsingleton (LocalizedModule S (Forms O Γ jK W)) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F

def FormsDevissage : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module T (Forms O Γ jK V)] (S : Submonoid T) (D₀ : Submodule O V)
    (D E : Submodule A V), IsNoetherian O V → IsArtinian O (V ⧸ D₀) → D₀ ≤ D.restrictScalars O →
    D ≤ E →
    (∀ F F' : Submodule A V, D ≤ F → F ⋖ F' → F' ≤ E →
      ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
        ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ E) →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ D

def cTau {ι : Type} [DecidableEq ι] (T2 : Finset ι) (ex c' : ι → ℕ) (τ : ι) : ℕ :=
  if τ ∈ T2 then min (ex τ) (c' τ) else ex τ

def TheoremWCore : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type) [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) [Module A (⨂[O] τ, Nb τ)]
    [IsScalarTower O A (⨂[O] τ, Nb τ)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (⨂[O] τ, Nb τ))] [IsScalarTower O T (Forms O Γ jK (⨂[O] τ, Nb τ))]
    (S : Submonoid T) (l ϖ : O) (n₀ : ℕ) (ω : Type) (pr : ∀ τ, ω → Nb τ →ₗ[O] Nb τ) (e : ι → ω → A)
    (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)] [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)]
    [∀ μ, IsScalarTower O A (L μ)] [∀ μ, Module T (Forms O Γ jK (L μ))]
    (hwt : Λ → ι → ω) (depth : ι → ω → ℤ) (i : ι → ℤ) (T2 : Finset ι) (ex c' : ι → ℕ),
    IsNoetherian O (⨂[O] τ, Nb τ) → IsArtinian O ((⨂[O] τ, Nb τ) ⧸ tensSub B) → l ∣ ϖ ^ n₀ →
    (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB B s), a • x ∈ tensSub (chainB B s)) →
    (∀ τ w (x : ⨂[O] τ, Nb τ), e τ w • x = atFactor τ (pr τ w) x) →
    HeckeStable O Γ jK T (⨂[O] τ, Nb τ) → (∀ μ, HeckeNat O Γ jK T (⨂[O] τ, Nb τ) (L μ)) →
    (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
      IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) →
    (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) →
    (∀ μ, IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) (L μ) →
      ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) → ∀ τ ∈ T2, depth τ (hwt μ τ) ≤ i τ) →
    (∀ τ, LatIncl l (B τ) (ex τ)) →
    (∀ τ ∈ T2, ∀ w, depth τ w ≤ i τ → ∀ x : Nb τ, l ^ c' τ • pr τ w x ∈ B τ) →
    ∀ y : LocalizedModule S (Forms O Γ jK (⨂[O] τ, Nb τ)),
      (algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • y ∈
        locSet S {x : Forms O Γ jK (⨂[O] τ, Nb τ) |
          (x : G → ⨂[O] τ, Nb τ) ∈ formsIn Γ K (repOf O jK (⨂[O] τ, Nb τ)) (tensSub B)}

abbrev NablaT (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) : Type :=
  ⨂[O] τ : ι, dualWeyl O N N (res N (lam τ))

def deltaIn (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (τ : ι) :
    Submodule O (dualWeyl O N N (res N (lam τ))) :=
  (weyl O N N le_rfl (res N (lam τ))).comap (dualWeyl O N N (res N (lam τ))).subtype

def depthAt (N k : ℕ) {ι : Type} (j : ι → ℕ) (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ) : ℤ :=
  depth2 (res N (varpi (k + j τ))) (res N (lam τ)) w

def cFloor (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl i : ι → ℕ)
    (τ : ι) : ℕ :=
  ⌊cPrime l k (j τ) t (q τ) h (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊

structure Shape (N k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ) : Prop where
  what₂ : k + j + t + q = N
  anti : ∀ a b, a ≤ b → b < N → lam b ≤ lam a
  block : ∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)
  spread : lam 0 + N ≤ h + lam (N - 1) + 1
  cloud : ∀ a, a < k → xm ≤ UN N lam a ∧ UN N lam a ≤ xp
  lows : ∀ a, k ≤ a → a < k + j → UN N lam a < xm
  above : UN N lam (k + j) < xm
  le : xm ≤ xp
  top : xp - UN N lam (k + j) ≤ (h : ℤ)

def TopInputs (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} [DecidableEq ι] (l N k t h : ℕ)
    (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) {Λ : Type} (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ) : Prop :=
  l.Prime ∧ (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) ∧ Finite (O ⧸ Ideal.span {(l : O)}) ∧
  (l : O) ∣ ϖ ^ n₀ ∧ h < l ^ 2 ∧ 1 ≤ t ∧
  (∀ τ ∈ T2, Shape N k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ)) ∧
  (∀ τ ∈ T2, ∀ μ : Fin k → ℕ, ExpLe l k (res k (lam τ)) μ (ecl τ)) ∧
  (∀ τ, LA.InclZ N N le_rfl (res N (lam τ)) l (ex τ)) ∧
  (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB (deltaIn O N lam) s),
    a • x ∈ tensSub (chainB (deltaIn O N lam) s)) ∧
  (∀ τ w (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O) →
    e τ w • PiTensorProduct.tprod O x = PiTensorProduct.tprod O (Function.update x τ y)) ∧
  HeckeStable O Γ jK T (NablaT O N lam) ∧ (∀ μ, HeckeNat O Γ jK T (NablaT O N lam) (L μ)) ∧
  (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
    IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) ∧
  (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) ∧
  (∀ μ, IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) (L μ) →
    ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) →
    ∀ τ ∈ T2, depthAt N k j lam τ (hwt μ τ) ≤ (i τ : ℤ))

def TopIncl (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} (l N : ℕ) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] {T : Type} [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (J : ℕ) : Prop :=
  ∀ y : LocalizedModule S (Forms O Γ jK (NablaT O N lam)),
    (algebraMap O T (l : O)) ^ J • y ∈
      locSet S {x : Forms O Γ jK (NablaT O N lam) |
        (x : G → NablaT O N lam) ∈ formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))}

def TheoremWTop : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def CPrimeLeCW5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (τ : ι) (l : ℕ), l.Prime → τ ∈ D.T2 → D.Params →
    cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ) (D.depth τ l : ℝ) ≤
      Cor.coefficientBoundTau D τ l

def LogPlusVsMax : Prop :=
  ∀ (l h : ℕ) (i : ℝ), 1 ≤ h → h < l → 0 < i →
    (i / (l : ℝ)) * max 0 (1 + Real.log ((h : ℝ) / (l : ℝ))) <
      (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def JointEstimate : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      D.J l ≤ ∑ τ, cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ) →
    Cor.BlockIdealBound5 D

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealAt : Prop :=
  LemmaDLastGraded →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (l : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O D.Nr lam)] [IsScalarTower O A (NablaT O D.Nr lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O D.Nr lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin D.Nr → ℕ),
    D.Params →
    TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
      (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt →
    (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) →
    D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J} →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ))

def WeightSpacePrimePowerBoundOverDomain : Prop :=
  LemmaDLastGraded → ∀ (R : Type) [CommRing R] [IsDomain R] (l N k j t q h : ℕ) (lam : ℕ → ℕ)
    (xm xp : ℤ) (ecl : ℕ), l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → h < l ^ 2 → 1 ≤ t →
    Shape N k j t q h lam xm xp → (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
    ∀ (I : ℕ) (w : Fin N → ℕ), depth2 (res N (varpi (k + j))) (res N lam) w ≤ (I : ℤ) →
      ∀ x ∈ nablaWtR R N (res N lam) w,
        (l : R) ^ ⌊cPrime l k j t q h ecl xm xp (UN N lam (k + j)) (I : ℝ)⌋₊ • x ∈
          weyl R N N le_rfl (res N lam)

def ExpLeOfInclZ : Prop :=
  ∀ (r : ℕ) (ν μ : Fin r → ℕ) (l e : ℕ), LA.InclZ r r le_rfl ν l e → ExpLe l r ν μ e

def ExactExponentsFit : Prop :=
  ∀ (l N k : ℕ) (lam : ℕ → ℕ), l.Prime → Antitone (res N lam) → Antitone (res k lam) →
    LA.InclZ N N le_rfl (res N lam) l (LA.exZ N N le_rfl (res N lam) l) ∧
      ∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ (LA.exZ k k le_rfl (res k lam) l)

def TopInclMono : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) (l N : ℕ) (lam : ι → ℕ → ℕ) [Module A (NablaT O N lam)]
    [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (NablaT O N lam))] [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))]
    (S : Submonoid T) (J J' : ℕ), J ≤ J' → TopIncl O Γ jK l N lam S J → TopIncl O Γ jK l N lam S J'

def cFloorCoarse (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ)
    (ecl i : ι → ℕ) (τ : ι) : ℕ :=
  ⌊cCoarse l k (j τ) t (q τ) h N (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊

def TheoremWTopCoarse : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloorCoarse l N k t h lam j q xm xp ecl i) τ)

open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealBound5Derived : Prop :=
  LemmaDLastGraded →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (A : Type) (_ : Ring A)
        (_ : Algebra O A) (G : Type) (_ : Group G) (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
        (_ : Module A (NablaT O D.Nr lam)) (_ : IsScalarTower O A (NablaT O D.Nr lam)) (T : Type)
        (_ : CommRing T) (_ : Algebra O T) (_ : Module T (Forms O Γ jK (NablaT O D.Nr lam)))
        (_ : IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))) (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
        (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) (_ : ∀ μ, AddCommGroup (L μ))
        (_ : ∀ μ, Module O (L μ)) (_ : ∀ μ, Module A (L μ)) (_ : ∀ μ, IsScalarTower O A (L μ))
        (_ : ∀ μ, Module T (Forms O Γ jK (L μ))) (hwt : Λ → ι → Fin D.Nr → ℕ),
        TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
          (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt ∧
        (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) ∧
        D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J}) →
    Cor.BlockIdealBound5 D

def DepthAsU : Prop :=
  ∀ (N c : ℕ) (lam : ℕ → ℕ) (w : Fin N → ℕ),
    depth2 (res N (varpi c)) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < c),
        (UN N lam a - ((w a : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)))

def WEDepth : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t (k + j + t + q) F) (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ)
    (kap : ι → Fin t → ℤ) (c : ι → ℕ) (τ : ι) (lam : ℕ → ℕ) (w : Fin (k + j + t + q) → ℕ),
    l.Prime → t + 2 * (h / (l - 1)) < l →
    WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → (∀ a, 0 ≤ U' τ a ∧ U' τ a ≤ (h : ℤ)) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (c τ : ℤ) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a →
    (∀ a, U τ a = UN (k + j + t + q) lam a) →
    (∀ a, U' τ a = (w a : ℤ) + ((k + j + t + q : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)) →
    depth2 (res (k + j + t + q) (varpi (k + j))) (res (k + j + t + q) lam) w ≤
      ((q * h + (l * mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) +
        mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ))) * (t + 2 * (h / (l - 1))) : ℕ) : ℤ)

def FilteredMap : Prop :=
  ∀ (C D : Type 1) [Category.{0} C] [Category.{0} D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : C → Prop) (P' : D → Prop),
    (∀ X, P X → P' (F.obj X)) → ∀ Y, Filtered P Y → Filtered P' (F.obj Y)

def FilteredExt : Prop :=
  ∀ (C : Type 1) [Category.{0} C] [Abelian C] (P : C → Prop) (S : ShortComplex C), S.ShortExact →
    Filtered P S.X₁ → Filtered P S.X₃ → Filtered P S.X₂

def FilteredTrans : Prop :=
  ∀ (C : Type 1) [Category.{0} C] [Abelian C] (P : C → Prop) (Y : C),
    Filtered (Filtered P) Y → Filtered P Y

def FilteredMapFiltered : Prop :=
  ∀ (C D : Type 1) [Category.{0} C] [Category.{0} D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : C → Prop) (P' : D → Prop),
    (∀ X, P X → Filtered P' (F.obj X)) → ∀ Y, Filtered P Y → Filtered P' (F.obj Y)

end Formalism.CohomologicalDescent.DepthNonnegative
end
end

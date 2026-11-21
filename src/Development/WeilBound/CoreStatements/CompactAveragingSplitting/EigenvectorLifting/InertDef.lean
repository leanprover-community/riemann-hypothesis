import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert

section
noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

structure IsFinAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : FinMaps F a a') (v : Pl F) : Prop where
  onto : (SB _).map (R.p v) = ⊤
  onto' : (SB _).map (R.p' v) = ⊤
  inv : augAt om v ≤ LinearMap.ker (R.p v)
  inv' : augAt om' v ≤ LinearMap.ker (R.p' v)
  equiv : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
    R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁'
  nontriv : Nontrivial (R.Pi v)
  irred : ∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤
  sph : v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0
  zeta : ∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩

def FinAt (Q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Chars F E → Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, Q F E X v →
      ∃ R, IsFinAt B G X om om' R v

def FinRam : Prop := FinAt fun _ _ _ _ _ _ _ X v => v ∈ X.T

def FinSplit : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ Nonempty (E →ₐ[F] Fv F v)

def FinInert : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ IsEmpty (E →ₐ[F] Fv F v)

theorem kFin_of (h1 : FinRam) (h2 : FinSplit) (h3 : FinInert) : GlobalTheory.ThK.KFin := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  have h : ∀ v, ∃ R, IsFinAt B G X om om' R v := fun v => by
    by_cases hv : v ∈ X.T
    · exact h1 F E σ B a a' G X om om' hT v hv
    · rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | he
      · exact h3 F E σ B a a' G X om om' hT v ⟨hv, he⟩
      · exact h2 F E σ B a a' G X om om' hT v ⟨hv, he⟩
  choose R hR using h
  exact ⟨{ Pi := fun v => (R v).Pi v, p := fun v => (R v).p v, p' := fun v => (R v).p' v },
    fun v => (hR v).onto, fun v => (hR v).onto', fun v => (hR v).inv, fun v => (hR v).inv', fun v => (hR v).equiv,
    fun v => (hR v).nontriv, fun v => (hR v).irred, fun v => (hR v).sph, fun v hv => (hR v.1).zeta v.2 hv⟩

end PositivityTheory.ThK
end
end

section
noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

abbrev Fn (F : Type) [Field F] [NumberField F] (n d : ℕ) (v : Pl F) : Type := (Fin n × Fin d → Fv F v) → ℂ

structure PairOK (B : Base F E) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) : Prop where
  base : B.IsGood σ
  herm : ∃ r s, X.IsHerm σ B r s
  skew : ∃ r s, W.IsSkew σ B r s
  good : M.IsGood B.ψ
  weil : ∃ χX χW, M.IsWeil B.ψ χX χW om

structure IsLocRep {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (v : Pl F)
    (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v))
    (ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)) : Prop where
  pres : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ω (g, h) φ ∈ SB _
  acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁,
    Acts (evFin F v) (om (g, h)) φ φ₁ ↔ φ₁ = ω (g, h) φ
  one : ∀ φ ∈ SB _, ω 1 φ = φ
  mul : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v),
    ∀ φ ∈ SB _, ω (g * g', h * h') φ = ω (g, h) (ω (g', h') φ)
  smooth : ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ h ∈ U, h ∈ UAt σ W (evFin F v) → ω (1, h) φ = φ
  presH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ρ u φ ∈ SB _
  actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ ↔ φ₁ = ρ u φ
  impl : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
    ω (g, h) (ρ u φ) = ρ (mat g * u * (mat h)ᵀ) (ω (g, h) φ)

def latW (W : Spc F E d) (v : Pl F) : AddSubgroup (Fin d → AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = fun i => a • inclR (F := F) (AF F) (y i)}

variable (σ) in

def KAt (W : Spc F E d) (v : Pl F) : Set (UA σ W.J) :=
  {k | k ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat k *ᵥ y ∈ latW W v ∧ mat k⁻¹ *ᵥ y ∈ latW W v}

variable (σ) in

structure IsLagAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Prop where
  rank : d = 2 * m
  supp : At (evFin F v) Cy
  iso : Cyᵀ * incM F W.J * Cy.map (cA σ) = 0
  free : ∀ t : Fin m → AE F E, At (evFin F v) t → Cy *ᵥ t = 0 → t = 0

variable (σ) in

def IsAdaptedAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Prop :=
  ∃ Cx : Matrix (Fin d) (Fin m) (AE F E), IsLagAt σ W v Cx ∧
    ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t

variable (σ) in

def PAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Set (UA σ W.J) :=
  {p | p ∈ UAt σ W (evFin F v) ∧ ∃ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t}

def IsEvAt {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {m : ℕ}
    (Cy : Matrix (Fin d) (Fin m) (AE F E)) (l : Fn F n d v →ₗ[ℂ] ℂ) : Prop :=
  ∀ z : Matrix (Fin n) (Fin m) (AE F E), ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ (z * Cyᵀ)) φ φ₁ → l φ₁ = l φ

def AllPairs (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    (_ : Base F E) {X : Spc F E n} {W : Spc F E d} (_ : Model σ X W) (_ : Rep σ X W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), PairOK B X W M om → ∀ v, Q B M om v

def LocRepEx : Prop := AllPairs fun B _ _ M om v => ∃ ω ρ, IsLocRep M B.ψ om v ω ρ

def KCompact : Prop := AllPairs fun {_ _} _ _ _ _ _ {σ _ _} _ _ W _ _ v => IsCompact (KAt σ W v)

def Iwasawa : Prop := AllPairs fun {F E} _ _ _ _ _ {σ _ d} _ _ W _ _ v => Even d → (∃ w, Formalism.UG.IsInertAt F E v w) →
  ∃ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy ∧ IsAdaptedAt σ W v Cy ∧
    (∀ h ∈ UAt σ W (evFin F v), ∃ p ∈ PAt σ W v Cy, ∃ k ∈ KAt σ W v, h = p * k) ∧
    ∀ c : UA σ W.J → ℂ, (∀ k ∈ KAt σ W v, ∀ k' ∈ KAt σ W v, c (k * k') = c k * c k') →
      (∀ k ∈ KAt σ W v, k ∈ PAt σ W v Cy → c k = 1) → ∀ k ∈ KAt σ W v, c k = 1

def EvLine : Prop := AllPairs fun {F E} _ _ _ _ _ {σ n d} B _ W M _ v => ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)),
  IsLagAt σ W v Cy → ∀ l l' : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l → IsEvAt M B.ψ v Cy l' → (∃ φ ∈ SB _, l φ ≠ 0) →
    ∃ c : ℂ, ∀ φ ∈ SB _, l' φ = c * l φ

def EvVac : Prop := AllPairs fun {F E} _ _ _ _ _ {σ n d} B _ W M _ v => (∃ w, Formalism.UG.IsInertAt F E v w) →
  ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy → IsAdaptedAt σ W v Cy →
    ∃ l : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l ∧ l (M.vac v) ≠ 0

def VacEigen : Prop := AllPairs fun {F _} _ _ _ _ _ {σ _ _} _ _ W M om v => ∀ k ∈ KAt σ W v,
  ∃ c : ℂ, Acts (evFin F v) (om (1, k)) (M.vac v) (c • M.vac v)

def InertOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∃ w, Formalism.UG.IsInertAt F E v w

def CoinvEmbeds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v w, Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (m : ℕ) (Cy : Matrix (Fin (a + a')) (Fin m) (AE F E)), IsLagAt σ G.W v Cy →
      (∀ l, IsEvAt G.M B.ψ v Cy l → (∃ φ ∈ SB _, l φ ≠ 0) → ∀ φ ∈ SB _, φ ∈ augAt om v ↔
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = 0) ∧
      ∀ l, IsEvAt G.M' B.ψ v Cy l → (∃ φ ∈ SB _, l φ ≠ 0) → ∀ φ ∈ SB _, φ ∈ augAt om' v ↔
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ₁, Acts (evFin F v) (om' (1, h)) φ φ₁ → l φ₁ = 0

end PositivityTheory.ThK
end
end

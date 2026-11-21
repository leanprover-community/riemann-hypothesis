import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

section
noncomputable section

open Polynomial Finset GlobalTheory.Cong

namespace UpperTheory.Gal.CharacterCongruences

section Approx

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

def PolyApproxAt (ε : ℝ) (θ : J → k) (S : Set (J → k)) : Prop :=
  ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

omit [IsUltrametricDist k] in

theorem PolyApproxAt.comp {ε : ℝ} {θ : J → k} {S : Set (J → k)} (h : PolyApproxAt ε θ S) {J' : Type} (f : J' → J) :
    PolyApproxAt ε (θ ∘ f) ((· ∘ f) '' S) := by
  classical
  obtain ⟨s, c, hs, hc⟩ := h
  refine ⟨s.image (· ∘ f), fun z => ∑ η ∈ s.filter (fun η => η ∘ f = z), c η, ?_, fun P => ?_⟩
  · rw [Finset.coe_image]; exact Set.image_mono hs
  · convert hc (MvPolynomial.rename f P) using 2
    rw [MvPolynomial.aeval_rename]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := (· ∘ f)) (t := s.image (· ∘ f)) fun η hη => Finset.mem_image_of_mem _ hη]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun η hη => ?_
    rw [MvPolynomial.aeval_rename, (Finset.mem_filter.1 hη).2]

end Approx

section Ring

variable (O : Type) [CommRing O] (l N m : ℕ)

def phi : O[X] := ∑ i ∈ range (l ^ m), X ^ (i * l ^ (N - m))

abbrev abelian₂ : Type := AdjoinRoot (phi O l N m)

def aug : abelian₂ O l N m →+* O ⧸ Ideal.span {(l : O) ^ m} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) 1 (by
    simp only [phi, eval₂_finset_sum, eval₂_X_pow, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _)

end Ring

def RingFree : Prop :=
  ∀ (O : Type) [CommRing O] (l N m : ℕ), 0 < l → m ≤ N →
    (phi O l N m).Monic ∧ phi O l N m * (X ^ (l ^ (N - m)) - 1) = X ^ (l ^ N) - 1 ∧
    Module.Free O (abelian₂ O l N m) ∧ Module.Finite O (abelian₂ O l N m) ∧ AdjoinRoot.root (phi O l N m) ^ (l ^ N) = 1

def RingInj : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (l N m : ℕ), 0 < l → m ≤ N →
    (∀ ζ : K, aeval ζ (phi O l N m) = 0 ↔ ζ ^ (l ^ N) = 1 ∧ ζ ^ (l ^ (N - m)) ≠ 1) ∧
    ((∃ z : K, IsPrimitiveRoot z (l ^ N)) → ∀ p : O[X],
      (∀ ζ : K, ζ ^ (l ^ N) = 1 → ζ ^ (l ^ (N - m)) ≠ 1 → aeval ζ p = 0) → AdjoinRoot.mk (phi O l N m) p = 0)

abbrev Ch (n : ℕ) : Type := Multiplicative (ZMod n) →* ℂˣ

def Regular : Prop :=
  ∀ (Γ M : Type) [Group Γ] [CommGroup M] (l : ℕ), l.Prime → ∀ (N c e r : ℕ), 0 < e → r * e ≤ l ^ c →
    ∀ (ψ : Γ →* Multiplicative (ZMod (l ^ N))), Function.Surjective ψ →
    ∀ (ξ : Multiplicative (ZMod (l ^ N)) →* M), ξ ^ (l ^ c) ≠ 1 →
    ∀ (ω ω' : Γ →* M) (n n' : ℕ), ω ^ e = 1 → ω' ^ e = 1 → n ≤ r → n' ≤ r → n ≠ n' →
      ω * (ξ.comp ψ) ^ n ≠ ω' * (ξ.comp ψ) ^ n'

def FourierCut : Prop :=
  ∀ (n M q : ℕ), 0 < n → n = M * q → ∃ (s : Finset (Ch n)) (c : Ch n → ℂ), (∀ ξ ∈ s, ξ ^ M ≠ 1) ∧
    ∀ x : Multiplicative (ZMod n), 1 - ∑ ξ ∈ s, c ξ * (ξ x : ℂ) = 0 ∨ 1 - ∑ ξ ∈ s, c ξ * (ξ x : ℂ) = q

def sys {k J : Type} [Field k] (ι : k ≃+* ℂ) {n : ℕ} (η : J → ℂ) (ξ : Ch n) : J ⊕ Multiplicative (ZMod n) → k :=
  Sum.elim (fun j => ι.symm (η j)) fun d => ι.symm (ξ d : ℂ)

def CongAbs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N m : ℕ), m ≤ N →
    ∀ (V X J : Type) [AddCommGroup V] [Module ℂ V] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ),
    (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) →
    ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → (∀ x, ‖ι.symm (ev x v₀)‖ ≤ 1) →
    ∀ (ℓ : X → Multiplicative (ZMod (l ^ N))) (S : Ch (l ^ N) → Set (J → ℂ)),
    (∀ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 → ∃ (d : ℕ) (v : Fin d → V) (η : Fin d → J → ℂ), (∀ i, η i ∈ S ξ) ∧
      (∀ i j, T j (v i) = η i j • v i) ∧ ∀ x, ev x (∑ i, v i) = (ξ (ℓ x) : ℂ) * ev x v₀) →
    PolyApproxAt (‖(l : PadicAlgCl l)‖ ^ m) (sys ι θ (1 : Ch (l ^ N)))
      {z | ∃ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 ∧ ∃ η ∈ S ξ, z = sys ι η ξ}

def ProjAbs : Prop :=
  ∀ (S V : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (t : Finset (Submodule ℂ V)),
    sSupIndep (t : Set (Submodule ℂ V)) → ∀ f : S →ₗ[ℂ] V, (∀ v, f v ∈ sSup (t : Set (Submodule ℂ V))) →
    ∃ F : Submodule ℂ V → S →ₗ[ℂ] V, (∀ U ∈ t, ∀ v, F U v ∈ U) ∧ (∀ v, ∑ U ∈ t, F U v = f v) ∧
      ∀ T : Module.End ℂ V, (∀ U ∈ t, ∀ φ ∈ U, T φ ∈ U) → ∀ v v', T (f v) = f v' → ∀ U ∈ t, T (F U v) = F U v'

end UpperTheory.Gal.CharacterCongruences

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep
open ValuativeRel

namespace UpperTheory.Gal.CharacterCongruences

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

structure IsLevel (C : Subgroup (UA E a)) : Prop where
  fin : C ≤ finU E a
  compact : IsCompact (C : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C

def NearOne {C : Subgroup (UA E a)} {D : Type} [Group D] (lam : C →* D) : Prop :=
  ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ ∀ c : C, c.1 ∈ N → lam c = 1

def RatNeat {C : Subgroup (UA E a)} {D : Type} [Group D] (lam : C →* D) : Prop :=
  ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c : C, ∀ x ∈ infU E a, γ * g = g * c * x → lam c = 1

def TorsFreeAt (K : Subgroup (UA E a)) (u : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ k ∈ K, IsOfFinOrder (cLoc u k) → cLoc u k = 1

def Rel {C : Subgroup (UA E a)} (A : Set (C →₀ ℂ)) (ψ : C →* ℂˣ) (φ : UA E a → ℂ) : Prop :=
  ∀ r ∈ A, (r.sum fun c z => (z * (((ψ c)⁻¹ : ℂˣ) : ℂ)) • RU E a c φ) = 0

structure OfVec (lam : (E →+* ℂ) → DomWeight a) (p : (UA E a → ℂ) → Prop) (U : Submodule ℂ (UA E a → ℂ)) : Prop where
  aut : IsAutRepU U
  wt : ∀ τ, HasWeightAt U τ (lam τ)
  vec : ∃ φ ∈ U, φ ≠ 0 ∧ p φ

def ActsOn {J : Type} (p : (UA E a → ℂ) → Prop) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) : Prop :=
  ∀ U, IsAutRepU U → ∀ φ ∈ U, p φ → ∀ j, opOf (RU E a) (t j) φ = η U j • φ

def CongFor (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N m : ℕ) (p : Ch (l ^ N) → (UA E a → ℂ) → Prop)
    (q : Submodule ℂ (UA E a → ℂ) → Prop) : Prop :=
  ∀ (lam : (E →+* ℂ) → DomWeight a) (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Ch (l ^ N) → Submodule ℂ (UA E a → ℂ) → J → ℂ), (∀ j, IsIntegralOp ι (t j)) →
    (∀ ξ : Ch (l ^ N), ξ = 1 ∨ ξ ^ (l ^ (N - m)) ≠ 1 → ActsOn (p ξ) t (η ξ)) → ∀ U, OfVec lam (p 1) U →
    PolyApproxAt (‖(l : Qbar l)‖ ^ m) (sys ι (η 1 U) (1 : Ch (l ^ N)))
      {z | ∃ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 ∧ ∃ U', OfVec lam (p ξ) U' ∧ q U' ∧ z = sys ι (η ξ U') ξ}

def CongC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ (C : Subgroup (UA E a)), IsLevel C → ∀ lam : C →* Multiplicative (ZMod (l ^ N)), NearOne lam → RatNeat lam →
    ∀ A : Set (C →₀ ℂ), CongFor l ι N m (fun ξ => Rel A (ξ.comp lam)) fun _ => True

def charRel {C : Type} [Group C] (χ : C →* ℂˣ) : Set (C →₀ ℂ) :=
  Set.range fun c => Finsupp.single c 1 - Finsupp.single 1 (χ c : ℂ)

def TypeW (w : HeightOneSpectrum (𝓞 E)) {K : Subgroup (UA E a)} (A : Set (K →₀ ℂ)) (ψ : K →* ℂˣ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (χ : J →* ℂˣ) (φ : UA E a → ℂ) : Prop :=
  Rel A ψ φ ∧ ∀ x ∈ locU a w, ∀ hx : cLoc w x ∈ J, RU E a x φ = (χ ⟨_, hx⟩ : ℂ) • φ

def CongW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ K : Subgroup (UA E a), IsLevelAway w K →
    ∀ (A : Set (K →₀ ℂ)) (lamK : K →* Multiplicative (ZMod (l ^ N))), NearOne lamK →
    ∀ J : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ((∃ u, Apart u w ∧ TorsFreeAt K u) ∨ ∀ x ∈ J, IsOfFinOrder x → x = 1) →
    ∀ (χ : J →* ℂˣ) (lam : J →* Multiplicative (ZMod (l ^ N))), IsOpen (lam.ker : Set J) →
    CongFor l ι N m (fun ξ => TypeW w A (ξ.comp lamK) (χ * ξ.comp lam)) fun _ => True

def CongSc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), 1 ≤ a → m ≤ N →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ∀ K : Subgroup (UA E a), IsLevelAway w₀ K →
    ∀ (A : Set (K →₀ ℂ)) (lamK : K →* Multiplicative (ZMod (l ^ N))), NearOne lamK →
    CongFor l ι N m (fun ξ => Rel A (ξ.comp lamK)) fun U => ScU U w₀

def blockChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s a : ℕ} {d : Fin s → ℕ}
    (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a) {M : Type} [CommGroup M] (ω : Fin s → (𝓀[k])ˣ →* M) : parahoric k e →* M :=
  ∏ b : Fin s, (ω b).comp ((Matrix.GeneralLinearGroup.det).comp
    ((Pi.evalMonoidHom (fun b => GL (Fin (d b)) 𝓀[k]) b).comp (parahoricProj k e)))

def CongP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ K : Subgroup (UA E a), IsLevelAway w K →
    ∀ u, Apart u w → TorsFreeAt K u → ∀ (A : Set (K →₀ ℂ)) (s : ℕ) (d : Fin s → ℕ) (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a)
    (ω : Fin s → (𝓀[w.adicCompletion E])ˣ →* ℂˣ) (ψ : (𝓀[w.adicCompletion E])ˣ →* Multiplicative (ZMod (l ^ N))) (n : Fin s → ℕ),
    CongFor l ι N m (fun ξ => TypeW w A 1 (blockChar e fun b => ω b * (ξ.comp ψ) ^ n b)) fun _ => True

def EllNeat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C →
    ∀ (D : Type) [AddCommGroup D] (lam : C →* Multiplicative D), NearOne lam → RatNeat lam →
    ∃ ℓ : UA E a → Multiplicative D, (∀ g, ∀ x ∈ infU E a, ℓ (g * x) = ℓ g) ∧ (∀ g (c : C), ℓ (g * c) = ℓ g * lam c) ∧
      ∀ F : Multiplicative D → ℂ, IsAutFormU fun g => F (ℓ g)

def NeatOfPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ u, TorsFreeAt C u →
    ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1

def FormIn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (lam : (E →+* ℂ) → DomWeight a) (Y U : Submodule ℂ (UA E a → ℂ)),
    (∀ x ∈ infU E a, ∀ φ ∈ Y, RU E a x φ ∈ Y) → OfVec lam (· ∈ Y) U →
    ∃ (W : Wt E a) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ ∀ v, f.1 v ∈ U ∧ f.1 v ∈ Y

def DecompKill : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (f : algForms W),
    ∃ (I : Finset (AutSub E a)) (F : AutSub E a → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ f = ∑ π ∈ I, F π ∧
      ∀ T : Module.End ℂ (UA E a → ℂ), (∀ U, IsAutRepU U → ∀ φ ∈ U, T φ ∈ U) → ∀ v, T (f.1 v) = 0 → ∀ π ∈ I, T ((F π).1 v) = 0

def LevelW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
    ∀ K : Subgroup (UA E a), IsLevelAway w K → ∀ J : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ∃ (C : Subgroup (UA E a)) (p : C →* K), IsLevel C ∧ K ≤ C ∧ (∀ x ∈ locU a w, cLoc w x ∈ J → x ∈ C) ∧ (∀ c ∈ C, cLoc w c ∈ J) ∧
      Continuous p ∧ (∀ c : C, c.1 ∈ K → (p c).1 = c.1) ∧ (∀ c : C, c.1 ∈ locU a w → p c = 1) ∧
      ∀ c : C, ((p c).1)⁻¹ * c.1 ∈ locU a w

def RelChar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)) (χ ψ : C →* ℂˣ) (φ : UA E a → ℂ),
    Rel (charRel χ) ψ φ ↔ ∀ c : C, RU E a c φ = ((χ * ψ) c : ℂ) • φ

def NearOneLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E))
    (J : Subgroup (GL (Fin a) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ∀ (hC : ∀ c ∈ C, cLoc w c ∈ J) (D : Type) [Group D] (lam : J →* D), IsOpen (lam.ker : Set J) →
    NearOne (lam.comp (((cLoc w).comp C.subtype).codRestrict J fun c => hC c.1 c.2))

def BlockOpen : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s a : ℕ) (d : Fin s → ℕ)
    (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a) (M : Type) [CommGroup M] (ω : Fin s → (𝓀[k])ˣ →* M),
    IsOpen ((blockChar e ω).ker : Set (parahoric k e))

end UpperTheory.Gal.CharacterCongruences

end
end

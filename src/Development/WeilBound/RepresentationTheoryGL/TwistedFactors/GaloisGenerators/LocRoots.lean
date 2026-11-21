import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Over (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal

def HasDeg (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (f : ℕ) : Prop :=
  Over w v ∧ Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f

def Above (S : Finset (HeightOneSpectrum (𝓞 F))) (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w v, Over w v → (w ∈ T ↔ v ∈ S)

def BCFam {S : Finset (HeightOneSpectrum (𝓞 F))} {T : Finset (HeightOneSpectrum (𝓞 E))} {n : ℕ}
    (α : Off F S → Fin n → ℂˣ) (A : Off E T → Fin n → ℂˣ) : Prop :=
  ∀ (w : Off E T) (v : Off F S) (f : ℕ), HasDeg w.1 v.1 f →
    Finset.univ.val.map (A w) = Finset.univ.val.map fun a => α v a ^ f

def IsGalGen (E : Type) [Field E] [NumberField E] [Algebra F E] (l : ℕ) (η : HChar F) : Prop :=
  η ≠ 1 ∧ η ^ l = 1 ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧
    ∀ w : HeightOneSpectrum (𝓞 E), Over w v → (HasDeg w v 1 ↔ η.val v = 1)

variable [IsTotallyComplex F] [IsTotallyComplex E]

def BCSat {n : ℕ} (π : CG F n) (w : HeightOneSpectrum (𝓞 E)) (C : Multiset ℂˣ) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 F)) (f : ℕ) (B : Multiset ℂˣ), HasDeg w v f ∧ π.HasSat v B ∧ C = B.map (· ^ f)

def IsWL {n : ℕ} (π : CG F n) {ι : Type} [Fintype ι] {m : ι → ℕ} (Ps : ∀ i, CG E (m i)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (C : Multiset ℂˣ) (B : ι → Multiset ℂˣ),
    BCSat π w C ∧ (∀ i, (Ps i).HasSat w (B i)) ∧ ∑ i, B i = C

def IsIso {n : ℕ} (P : CG E n) {ι : Type} [Fintype ι] {m : ι → ℕ} (Ps : ∀ i, CG E (m i)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (C : Multiset ℂˣ) (B : ι → Multiset ℂˣ),
    P.HasSat w C ∧ (∀ i, (Ps i).HasSat w (B i)) ∧ ∑ i, B i = C

variable (E) in

def SameBC {n : ℕ} (π π' : CG F n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ C : Multiset ℂˣ, BCSat π w C ∧ BCSat π' w C

end PositivityTheory.Rg.Tf.ChR
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def ChapterR : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l →
    (∃ η : HChar F, IsGalGen E l η) ∧
    (∀ (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ) (Ps : ∀ i, CG E (m i)),
      1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps) ∧
    ∀ η : HChar F, IsGalGen E l η →
      (∀ (n n' : ℕ) (π : CG F n) (π' : CG F n'), 1 ≤ n → 1 ≤ n' → π.IsUnitary → π'.IsUnitary →
        ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Above S T →
          ∀ (α : Off F S → Fin n → ℂˣ) (β : Off F S → Fin n' → ℂˣ) (A : Off E T → Fin n → ℂˣ)
            (B : Off E T → Fin n' → ℂˣ), SatOff π S α → SatOff π' S β → BCFam α A → BCFam β B →
            ∀ s : ℂ, 2 < s.re → LS T A B s = ∏ k : Fin l, LS S α (fun v b => β v b * η.val v.1 ^ (k : ℕ)) s) ∧
      (∀ (n : ℕ) (π π' : CG F n), 1 ≤ n → SameBC E π π' → ∃ k : ℕ, k < l ∧ π' = π.twist (η ^ k)) ∧
      (∀ (n : ℕ) (π : CG F n) (ι : Type) [Fintype ι] (m : ι → ℕ) (Ps : ∀ i, CG E (m i)),
        1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → IsWL π Ps →
          ∃ k : ℕ, 0 < k ∧ k < l ∧ π = π.twist (η ^ k)) ∧
      (∀ (n : ℕ) (π : CG F n) (P : CG E n), 1 ≤ n → IsWL π (ι := Unit) (m := fun _ => n) (fun _ => P) →
        ∀ k : ℕ, 0 < k → k < l → π ≠ π.twist (η ^ k))

end PositivityTheory.Rg.Tf.ChR
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def PartE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l → ∃ η : HChar F, IsGalGen E l η

def PartA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (Ps : ∀ i, CG E (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps

def PartB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l → ∀ η : HChar F, IsGalGen E l η →
    ∀ (n n' : ℕ) (π : CG F n) (π' : CG F n'), 1 ≤ n → 1 ≤ n' → π.IsUnitary → π'.IsUnitary →
      ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Above S T →
        ∀ (α : Off F S → Fin n → ℂˣ) (β : Off F S → Fin n' → ℂˣ) (A : Off E T → Fin n → ℂˣ)
          (B : Off E T → Fin n' → ℂˣ), SatOff π S α → SatOff π' S β → BCFam α A → BCFam β B →
          ∀ s : ℂ, 2 < s.re → LS T A B s = ∏ k : Fin l, LS S α (fun v b => β v b * η.val v.1 ^ (k : ℕ)) s

def PartC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l → ∀ η : HChar F, IsGalGen E l η →
    ∀ (n : ℕ) (π π' : CG F n), 1 ≤ n → SameBC E π π' → ∃ k : ℕ, k < l ∧ π' = π.twist (η ^ k)

def PartD : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l → ∀ η : HChar F, IsGalGen E l η →
    ∀ (n : ℕ) (π : CG F n) (ι : Type) [Fintype ι] (m : ι → ℕ) (Ps : ∀ i, CG E (m i)),
      1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → IsWL π Ps →
        ∃ k : ℕ, 0 < k ∧ k < l ∧ π = π.twist (η ^ k)

def PartF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l → ∀ η : HChar F, IsGalGen E l η →
    ∀ (n : ℕ) (π : CG F n) (P : CG E n), 1 ≤ n → IsWL π (ι := Unit) (m := fun _ => n) (fun _ => P) →
      ∀ k : ℕ, 0 < k → k < l → π ≠ π.twist (η ^ k)

def LocRoots : Prop :=
  ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l → ∀ x : ℂ, ∏ k : Fin l, (1 - x * ζ ^ (k : ℕ)) = 1 - x ^ l

def RootsMs : Prop :=
  ∀ (l : ℕ) (ζ : ℂˣ), l.Prime → IsPrimitiveRoot ζ l → ∀ B B' : Multiset ℂˣ, B.map (· ^ l) = B'.map (· ^ l) →
    ∑ k : Fin l, B.map (· * ζ ^ (k : ℕ)) = ∑ k : Fin l, B'.map (· * ζ ^ (k : ℕ))

def SplitUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime →
    Module.finrank F E = l → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (Nat.card {w : HeightOneSpectrum (𝓞 E) // Over w v} = l ∧ ∀ w : HeightOneSpectrum (𝓞 E), Over w v → HasDeg w v 1) ∨
      (Nat.card {w : HeightOneSpectrum (𝓞 E) // Over w v} = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 E), Over w v → HasDeg w v l)

def PairNZ : Prop := ForSys fun q X _ A => ∀ x y : X, x ≠ y → ∀ (G : ℂ → ℂ) (σ₀ : ℝ),
  (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) → (∀ σ : ℝ, σ₀ < σ → G σ = eul q (A x) (A y) σ) → G 1 ≠ 0

def DiagNZ : Prop := ForSys fun q X _ A => ∀ (x : X) (G : ℂ → ℂ) (σ₀ : ℝ),
  (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) → (∀ σ : ℝ, σ₀ < σ → G σ = ((σ : ℂ) - 1) * eul q (A x) (A x) σ) → G 1 ≠ 0

def shf {W : Type} (q : W → ℕ) {X : Type} {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} (x : ι → X × ℝ) :
    W → (Σ i, Fin (d (x i).1)) → ℂ :=
  fun w p => A (x p.1).1 w p.2 * (q w : ℂ) ^ (-((x p.1).2 : ℂ))

def PoleOne : Prop := ForSys fun q X _ A => ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x : ι → X × ℝ),
  (∀ w, ‖∏ p, shf q A x w p‖ = 1) →
  (∃ (G : ℂ → ℂ) (σ₀ : ℝ), (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) ∧
    ∀ σ : ℝ, σ₀ < σ → G σ = ((σ : ℂ) - 1) * eul q (shf q A x) (shf q A x) σ) →
  Subsingleton ι ∧ ∀ i, (x i).2 = 0

end PositivityTheory.Rg.Tf.ChR
end
end

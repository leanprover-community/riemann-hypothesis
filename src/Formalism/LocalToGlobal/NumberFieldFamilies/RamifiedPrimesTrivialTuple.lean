import Formalism.LocalToGlobal.UnitaryNorms.CharDiv
import Formalism.LocalToGlobal.UnitaryNorms.UnrAEPf

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

def QpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Set ℕ :=
  {p | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}

def QPlSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | Tp.InQ' μ v}

def XiRamFin (Tp : TupTied D C nch) : Prop :=
  ∀ μ, (QpSet Tp μ).Finite ∧ (QPlSet Tp μ).Finite

def XiUnrG (Tp : TupTied D C nch) : Prop :=
  ∀ μ i w, OverP D.host (D.host.g i) w → (Tp.xi μ).UnrAt w

def QDegOne (Tp : TupTied D C nch) : Prop :=
  ∀ μ v, Tp.InQ' μ v → (Ideal.absNorm v.asIdeal).Prime

def QpOf (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ : D.what₂.Tup) : Finset ℕ := (hf μ).1.toFinset

def QPlOf (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Type := {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}

@[instance_reducible] def finQOf (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ : D.what₂.Tup) : Fintype (QPlOf Tp μ) := (hf μ).2.fintype

def qvOf (Tp : TupTied D C nch) (μ : D.what₂.Tup) (v : QPlOf Tp μ) : ℕ := Ideal.absNorm v.1.asIdeal


theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ ψ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (hχ : χ.UnrAt w) (hψ : ψ.UnrAt w) : (χ * ψ).UnrAt w := fun x hx => by
  show χ.loc w x * ψ.loc w x = 1
  rw [hχ x hx, hψ x hx, one_mul]

theorem overP_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : (1 : 𝓞 D.host.E) ∈ w.asIdeal := by
    have e : ((a : ℤ) : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + ((b : ℤ) : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
      push_cast at this
      exact this
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1')

theorem delAt_unr (l : ℕ) (hl : l.Prime) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : OverP D.host l w) :
    (C.delAt l).UnrAt w := by
  unfold CharFrame.delAt
  split_ifs with h
  · refine C.isDel'.unr w fun h' => D.host.pde_ne ?_
    rw [← h]
    exact overP_unique hl D.host.pde'_prime hw h'
  · refine C.isDel.unr w fun h' => h ?_
    exact overP_unique hl D.host.pde_prime hw h'







def mult (P : HeightOneSpectrum (𝓞 D.host.E)) (I : Ideal (𝓞 D.host.E)) : ℕ :=
  Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)

def vddOf (pr : ℕ → D.what₂.Tau → HeightOneSpectrum (𝓞 D.host.E)) (p : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if p.Prime then
    (mult (pr p τ) (differentIdeal ℤ (𝓞 D.host.E)) : ℝ) / (mult (pr p τ) (Ideal.span {((p : ℕ) : 𝓞 D.host.E)}) : ℝ)
  else 0





def XiRamFinE (Tp : TupTied D C nch) : Prop :=
  ∀ μ, {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ (Tp.xi μ).UnrAt w}.Finite




structure ConjAt (D : D7) where
  M : ℕ → Type
  [instM : ∀ j, NormedAddCommGroup (M j)]
  [instMi : ∀ j, InnerProductSpace ℂ (M j)]
  [instMf : ∀ j, FiniteDimensional ℂ (M j)]
  T : ℕ → Type
  [instT : ∀ j, NormedAddCommGroup (T j)]
  [instTi : ∀ j, InnerProductSpace ℂ (T j)]
  [instTf : ∀ j, FiniteDimensional ℂ (T j)]
  th : ∀ j, T j →ₗ[ℂ] M j
  part : ∀ j, D.what₂.FT → Submodule ℂ (M j)

attribute [instance] ConjAt.instM ConjAt.instMi ConjAt.instMf ConjAt.instT ConjAt.instTi ConjAt.instTf

def lamAt (A : ConjAt D) (j : ℕ) (π : D.what₂.FT) : ℝ :=
  (LinearMap.trace ℂ (A.M j) (A.th j ∘ₗ LinearMap.adjoint (A.th j) ∘ₗ
    ((A.part j π).starProjection : A.M j →ₗ[ℂ] A.M j))).re / (Module.finrank ℂ (A.part j π) : ℝ)

open Classical in

def logLamOf (A : (D.what₂.LL →+* ℂ) → ConjAt D) (j : ℕ) (π : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j π) else Real.log (lamAt (A e) j π)


end Formalism.L2.Fam.DivCQ

end

module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.BaseEx
public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.GlobalTheory.JetPositivity.DeltaPowTwelveEqDiscr
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

structure CarRows (R : Ranks) where
  Tau : Type
  [instTau : Fintype Tau]
  card_Tau : Fintype.card Tau = R.f

attribute [instance] CarRows.instTau

structure Car where
  R : Ranks
  host : Host R
  what₂ : CarRows R
  eTau : what₂.Tau ≃ (R.Psi)

def Car.ofRec (D : D7) : Car := ⟨D.R, D.host, ⟨D.what₂.Tau, D.what₂.card_Tau⟩, D.eTau⟩

end Formalism.L2.Ker

namespace Formalism.L2.Ker.Cd.TaylorLogMetric

open Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def embT (D : Car) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau τ : D.R.GG)

def homL (D : Car) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl (D : Car) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E)
    {B | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ A ∈ homL D L L', B = a • A}

def hYY (D : Car) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : D.host.K :=
  Algebra.trace D.host.K D.host.E (∑ i, ∑ j, x i j * D.host.conj (y i j))

def lamOf (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E))}

def IsCurveIdeal (D : Car) (cc : Ideal (𝓞 D.host.K)) : Prop :=
  cc ≠ ⊥ ∧ Nat.Coprime (Ideal.absNorm cc) (2 * D.host.d)

def IsDiscriminantTwelfthRootOfIdealLattice (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  δ ^ 12 = discr (lamOf D cc 1)

structure Tor (D : Car) where
  emb : D.what₂.Tau → D.host.E → ℂ
  abelian₂ : AddSubgroup ℂ

abbrev VC (D : Car) (N N' : ℕ) : Type := D.what₂.Tau → Fin N' → Fin N → ℂ

def tor0 (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ => embT D τ, lamOf D cc δ⟩

def embV (D : Car) (T : Tor D) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' :=
  fun τ i j => T.emb τ (A i j)

def La (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : AddSubgroup (VC D N N') :=
  AddSubgroup.closure {z | ∃ w ∈ T.abelian₂, ∃ A ∈ YYl D L L', z = w • embV D T A}

def Hf (D : Car) (T : Tor D) {N N' : ℕ} (z w : VC D N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (area T.abelian₂ : ℂ)

def al (D : Car) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re))

def U (D : Car) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)

def ThSp (D : Car) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N')) : Set (VC D N N' → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z}

def Th (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (VC D N N' → ℂ) :=
  ThSp D T (La D T L L')

def Iop (D : Car) (T : Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z

def pull (D : Car) (T : Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun z => G (fun τ => (Matrix.conjTranspose (γ'.map (T.emb τ)) * (Matrix.of (z τ)) * γ.map (T.emb τ) : Matrix _ _ ℂ))

abbrev FamE (D : Car) : Type :=
  ∀ (N N' : ℕ), Submodule (𝓞 D.host.E) (Fin N → D.host.E) →
    Submodule (𝓞 D.host.E) (Fin N' → D.host.E) → VC D N N' → ℂ

def admitted (D : Car) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  letI := D.host.cmStar
  Even N ∧ Even N' ∧ IsSDLat D.host.E N L ∧ IsSDLat D.host.E N' L'

abbrev IdE (D : Car) : Type := Submodule (𝓞 D.host.E) D.host.E

def N1 (D : Car) (𝔞 : IdE D) : Prop :=
  ∃ 𝔟 : IdE D, (∀ x, x ∈ 𝔟 ↔ D.host.conj x ∈ 𝔞) ∧ 𝔞 * 𝔟 = 1

def detId (D : Car) {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def IsChi (D : Car) (χ : IdE D → ℂ) : Prop :=
  (∀ 𝔞 𝔟, N1 D 𝔞 → N1 D 𝔟 → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
  letI := D.host.cmStar
  ∀ z : unitary D.host.E,
    χ (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) = ∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹

def eq22 (D : Car) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => (χ (detId D L'.1 L''.1)) ^ (-((N / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => (χ (detId D L.1 L₁.1)) ^ (((N' / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

end Formalism.L2.Ker.Cd.TaylorLogMetric

namespace Formalism.L2.Ker.Cd

open NumberField Formalism.BasicNotions Classical

def StandardLatticesGL3.stdL (D : Car) (N : ℕ) : Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

def GL3Theta.IsTwoTorsionPointUnkilled (D : Car) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

open scoped BigOperators ComplexConjugate Pointwise
open Formalism.L2.Ker.Base (Comm)

open Formalism.L2.Th1.H (Sesq matH stdH stdLat alphaQ kernel4 tens4 StdData pow4 imgLat inter opU)
open Formalism.MainNotions

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]

end Gen

section Arith

variable (D : Car)

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1

abbrev IsoK : Type := IsoKG D.host.K D.host.E D.host.conj D.what₂.Tau

variable {D}

def IsoK.AtP (γ : IsoK D) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : D.host.K) * γ.g x w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧
  ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : D.host.E) * γ.g.symm v a ∈ D.host.AA0

def IsoK.detRel (γ γ₀ : IsoK D) : D.host.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] _) :
    (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K))

def ordK (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (x : D.host.K) : ℤ :=
  -WithZero.log (𝔭.valuation D.host.K x)

structure KapChoice (γ₀ : IsoK D) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)
  pp_over : ∀ p, p.Prime → SplitK D p → ((p : ℕ) : 𝓞 D.host.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 D.host.K
  pi_gen : ∀ p, p.Prime → SplitK D p → (pp p).asIdeal ^ classNumber D.host.K = Ideal.span {pi p}
  gaP : ℕ → IsoK D
  gaP_at : ∀ p, p.Prime → SplitK D p → (gaP p).AtP p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK D p → rt p ^ (2 * classNumber D.host.K)
    = D.host.φ₀ (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)
      / D.host.φ₀ (D.host.conj (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))

def KapChoice.yP {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) : ℤ := ordK (k.pp p) ((k.gaP p).detRel γ₀)

def KapChoice.kappa {γ₀ : IsoK D} (k : KapChoice γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, k.rt p ^ (-(k.yP p))

def lamMM (D : Car) (Λ : AddSubgroup ℂ) : AddSubgroup (D.what₂.Tau → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ D.host.AA0, z = fun τ => w * TaylorLogMetric.embT D τ a}

end Arith

section Fam

variable {D : Car}

structure Base (D : Car) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ
  ω₀ : ℂ
  t0 : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀ / 2)
  γ₀ : IsoK D
  gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)
  gC_spec : ∀ x : Fin 4 → D.host.E, gC (fun w => TaylorLogMetric.embT D w.2 (x w.1))
    = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)
  kc : KapChoice γ₀

namespace Base

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def cq (_B : Base D cc δ) : ℝ := Real.sqrt D.host.d / 2

def lamM (_B : Base D cc δ) : AddSubgroup (D.what₂.Tau → ℂ) := lamMM D (TaylorLogMetric.lamOf D cc δ)

def kappa : ℂ := B.kc.kappa

def StdOK : Prop := Ker.StdOK B.L B.ω₀ B.cq B.lamM B.gC

def IsThMM (θ : (D.what₂.Tau → ℂ) → ℂ) : Prop := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa θ

def thMM : (D.what₂.Tau → ℂ) → ℂ := thM B.L B.ω₀ B.cq B.lamM B.gC B.kappa

def thZero (N N' : ℕ) : TaylorLogMetric.VC D N N' → ℂ := tensPow B.thMM N N'

abbrev tor (_B : Base D cc δ) : TaylorLogMetric.Tor D := TaylorLogMetric.tor0 D cc δ

def thHalf (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
    (B.thZero N N')

def thMoved (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : TaylorLogMetric.VC D N N' → ℂ :=
  TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thHalf N N' L)

def chiFac (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : ℂ :=
  χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))

def eNat (χ : TaylorLogMetric.IdE D → ℂ) : TaylorLogMetric.FamE D :=
  fun N N' L L' z => chiFac χ N N' L L' * B.thMoved N N' L L' z

def AreaOK : Prop := TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L

def Lat0OK (N N' : ℕ) : Prop :=
  TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N'

def LatOK (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  Formalism.L2.Th1.H.IsSelfDual (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') ∧
  Formalism.L2.Th1.H.IsSemiChar (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L')
    (TaylorLogMetric.al D B.tor)

def ThZeroMem (N N' : ℕ) : Prop :=
  B.thZero N N' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))

def QInt0 (N N' : ℕ) : Prop :=
  ∀ x ∈ TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'), ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def QIntAll : Prop :=
  ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → ∀ x ∈ TaylorLogMetric.La D B.tor L L', ∃ m : ℤ,
    Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor x x).re = (m : ℝ)

def ThZeroSpans (N N' : ℕ) : Prop :=
  ∀ F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
    (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), ∃ a : ℂ, F = a • B.thZero N N'

def LatAll : Prop :=
  (∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → B.LatOK N N' L L') ∧
  ∀ N N' L₁ L₁' L₂ L₂', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.admitted D N N' L₂ L₂' →
    Comm (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂')

def EqP (χ : TaylorLogMetric.IdE D → ℂ) : Prop := TaylorLogMetric.eq22 D B.tor χ (B.eNat χ)

end Base

end Fam

open Formalism.MainNotions

section HostFacts

variable (D : Car)

def KQuad : Prop := Module.finrank ℚ D.host.K = 2

def EmbOnK : Prop :=
  ∀ (τ : D.what₂.Tau) (k : D.host.K), TaylorLogMetric.embT D τ (algebraMap D.host.K D.host.E k) = D.host.φ₀ (k : D.host.E)

def PhiNonReal : Prop := ∃ k : D.host.K, (D.host.φ₀ (k : D.host.E)).im ≠ 0

def PeriodExists : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∃ L : PeriodPair, L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ

end HostFacts

open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Seam

open Formalism.MainNotions

structure Seam (D : Car) (X : Fields) where
  iE : X.E ≃+* D.host.E
  iT : X.Tau ≃ D.what₂.Tau
  σ₀ : X.K →+* ℂ

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.Ok : Prop :=
  (∀ τ x, s.σ₀ (X.emb τ x) = TaylorLogMetric.embT D (s.iT τ) (s.iE x)) ∧ ∀ x, s.iE (star x) = D.host.conj (s.iE x)

def Seam.lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (N : Set (Sp X.E n)))

def ambOf {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := cD (s.iT τ)
  e a b N N' z := B.eNat χ a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')

end Seam

end Formalism.L2.Ker.Cd

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

namespace Formalism.L2.Ker

open Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section OverColDat

variable (d : ColDat)

variable {d}

end OverColDat

end Formalism.L2.Ker

import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

section
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine mcPts)

noncomputable section

instance isPrime_span_prime (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2 (Nat.prime_iff_prime_int.1 p.2)

abbrev ZP (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

instance (p : Nat.Primes) : IsDiscreteValuationRing (ZP p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (P := Ideal.span {((p : ℕ) : ℤ)})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero) (ZP p)

variable {K : Type} {ι : K → Type} {σ : Type}

def extTo (R : Type) [CommRing R] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) : Ideal (MvPolynomial (Σ k, ι k) R) :=
  P.map (MvPolynomial.map (Int.castRingHom R))

def LocPair.IsVertOff [DecidableEq K] (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ))
    (S : Finset Nat.Primes) : Prop :=
  ∀ i, (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.g i) bg ∧
      (fun k => (bf k : ℤ) - bg k) = T.x i - T.x' i) ∧ T.f i ∉ P ∧ T.g i ∉ P ∧
    ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * T.f i - v * T.g i ∈ P

def LocPair.linNum [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) :
    MvPolynomial (Σ k, ι k) R :=
  ∏ i, T.f i ^ (la i).toNat * T.g i ^ (-la i).toNat

def LocPair.linDen [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) :
    MvPolynomial (Σ k, ι k) R :=
  ∏ i, T.g i ^ (la i).toNat * T.f i ^ (-la i).toNat

def LocPair.lin [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) : LocPair ι R Unit :=
  ⟨fun _ => ∑ i, la i • T.x i, fun _ => ∑ i, la i • T.x' i, fun _ => T.linNum la, fun _ => T.linDen la⟩

variable [Fintype K]

def LocPair.IsIsometric (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A A' : σ → HermLine ι) :
    Prop :=
  ∀ i, (A i).a = T.x i ∧ (A' i).a = T.x' i ∧ ∀ z ∈ mcPts P,
    ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f i))‖ * (A' i).h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g i))‖ * (A i).h z

def arList (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (l : List (HermLine ι)) : ℝ :=
  I P l.length l.get

def arNum (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι) (H : MvPolynomial σ ℝ) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * arList I P (μ.toMultiset.map A).toList

def HasConstants (R A : Type) [CommRing R] [CommRing A] {Ω : Type} [Field Ω] [Algebra R Ω] [Algebra A Ω]
    (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c, GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y c ≠ 0 → ∀ a : A,
    algebraMap A Ω a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing R (GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y) c

end

end GlobalTheory.CompanionTheory.Ar.Num
end

section
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsConjInvariantH IntersectionSystem)
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal divCycle cycEval intNumL)

noncomputable section

open Classical in

def vertAt {K : Type} [DecidableEq K] {ι : K → Type} (p : Nat.Primes) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ))
    (f : MvPolynomial (Σ k, ι k) ℤ) (l : List (K → ℤ)) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  cycEval (fun W => if (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W then
    intNumL (ZMod p) (extTo (ZMod p) W) l else 0) (divCycle P f)

def AtPlacesOver (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω] (p : ℕ)
    (Pr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω], Prop) : Prop :=
  ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O]
      [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], Pr O

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

structure SecondRoots (M : RootModel Ψ N) where

  xdeg : Ψ × Fin N → M.K → ℤ

  x : ℝ → Ψ × Fin N → HermLine M.ι
  x_deg : ∀ t r, (x t r).a = xdeg r
  x_smooth : ∀ t r, IsSmoothHerm (x t r)
  x_conj : ∀ t r, IsConjInvariantH (x t r)

  f : Ψ × Fin N → MvPolynomial (Σ k, M.ι k) ℤ

  g : Ψ × Fin N → MvPolynomial (Σ k, M.ι k) ℤ

variable {M : RootModel Ψ N}

def SecondRoots.model (R : SecondRoots M) : RootModel Ψ N :=
  { M with xdeg := R.xdeg, x := R.x, x_deg := R.x_deg, x_smooth := R.x_smooth, x_conj := R.x_conj }

def SecondRoots.pairs (R : SecondRoots M) : LocPair M.ι ℤ (Ψ × Fin N) := ⟨M.xdeg, R.xdeg, R.f, R.g⟩

open Classical in

def SecondRoots.IsChange (R : SecondRoots M) (S : Finset Nat.Primes) : Prop :=
  R.pairs.IsVertOff M.P S ∧ ∀ t, 0 < t → R.pairs.IsIsometric M.P (M.x t) (R.x t)

open Classical in

def SecondRoots.LocalAt [DecidableEq Ψ] (R : SecondRoots M) (j p : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (P : Ideal (MvPolynomial (Σ k, M.ι k) O)) : Prop :=
  FlagChernComparison P (dimFl Ψ N) p j φ (R.pairs.map (Int.castRingHom O)) ∧
    ∀ τ, PowerSumsVanish P (dimFl Ψ N) fun i : Fin N => R.xdeg (τ, i)

def SecondRoots.LocalAtPlaces [DecidableEq Ψ] (R : SecondRoots M) (j : ℕ) (S : Finset Nat.Primes)
    (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDedekindDomain A) (_ : Module.Finite ℤ A) (_ : Algebra A M.Ω),
    Function.Injective (algebraMap A M.Ω) ∧ HasConstants ℤ A M.y ∧
    ∀ p ∈ S, AtPlacesOver A M.Ω p fun O _ _ _ _ => R.LocalAt j p (φ p) O (pointIdeal O M.y)

open Classical in

def LinkedTower [DecidableEq Ψ] (T : RootTower Ψ N) (II : IntersectionSystem) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)) : Prop :=
  ∀ B₀ B : ℕ, 2 ≤ B₀ → B₀ ≤ B → ∀ c, ∃ (M : RootModel Ψ N) (R : SecondRoots M) (S : Finset Nat.Primes),
    (∀ p : Nat.Primes, p ∈ S ↔ B₀ < (p : ℕ) ∧ (p : ℕ) ≤ B ∧ (p : ℕ) ∉ T.bad) ∧
    M.Converges II ∧ R.model.Converges II ∧
    (∀ F : RP Ψ N, M.PP II (toA F) = T.PPc II B₀ c F) ∧ (∀ F : RP Ψ N, R.model.PP II (toA F) = T.PPc II B c F) ∧
    (∀ F : RP Ψ N, M.geoFun (toA F) = (T.M B₀ c).geoFun (toA F)) ∧
    R.IsChange S ∧ R.LocalAtPlaces T.j S φ

end

end GlobalTheory.CompanionTheory.Ar.Num
end

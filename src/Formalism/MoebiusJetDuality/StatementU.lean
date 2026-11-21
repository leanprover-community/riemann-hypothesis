import Mathlib
import Formalism.RealPlaceAnalysis.FockPairGl
import Formalism.SatakeDualWeyl.Statement

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial
open scoped Kronecker

universe u v

def linSubst {σ : Type u} {R : Type v} [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) : MvPolynomial σ R :=
  aeval (fun i => ∑ j, C (g i j) * X j) f

def IsIntegralJet {σ : Type u} {R : Type v} [CommRing R] (A : Subring R)
    (f : MvPolynomial σ R) : Prop :=
  ∀ α, coeff α f ∈ A

def IsIntegralMat {ι κ : Type u} {R : Type v} [CommRing R] (A : Subring R)
    (g : Matrix ι κ R) : Prop :=
  ∀ i j, g i j ∈ A

def mfac {σ : Type u} (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

def evOp {σ : Type u} {R : Type v} [CommRing R] (P F : MvPolynomial σ R) : R :=
  ∑ α ∈ P.support, (mfac α : R) * coeff α P * coeff α F

def jetTrunc {σ : Type u} {R : Type v} [CommRing R] (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  ∑ n ∈ Finset.range (N + 1), homogeneousComponent n f

def hcMat {R : Type v} [CommRing R] {p q : ℕ} (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R) : Matrix (Fin p × Fin q) (Fin p × Fin q) R :=
  A ⊗ₖ D.transpose

def actK {R : Type v} [CommRing R] {p q r : ℕ}
    (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R) :
    Fin r → MvPolynomial (Fin p × Fin q) R :=
  fun i => ∑ j, C ((ρ k : Matrix (Fin r) (Fin r) R) i j) *
    linSubst (hcMat ((k.1⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R)
      ((k.2 : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) (F j)

def LinSubstOne : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (f : MvPolynomial σ R),
    linSubst (1 : Matrix σ σ R) f = f

def LinSubstMul : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g h : Matrix σ σ R)
    (f : MvPolynomial σ R),
    linSubst (g * h) f = linSubst h (linSubst g f)

def LinSubstHomog : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) (n : ℕ),
    homogeneousComponent n (linSubst g f) = linSubst g (homogeneousComponent n f)

def JetTruncSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) (N : ℕ),
    jetTrunc N (linSubst g f) = linSubst g (jetTrunc N f)

def ScaleHomog : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (c : R)
    (f : MvPolynomial σ R) (n : ℕ),
    homogeneousComponent n (linSubst (c • (1 : Matrix σ σ R)) f) =
      c ^ n • homogeneousComponent n f

def IntSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (A : Subring R) (g : Matrix σ σ R)
    (f : MvPolynomial σ R),
    IsIntegralMat A g → IsIntegralJet A f → IsIntegralJet A (linSubst g f)

def IntSubstIff : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (A : Subring R)
    (g h : Matrix σ σ R) (f : MvPolynomial σ R),
    IsIntegralMat A g → IsIntegralMat A h → g * h = 1 →
      (IsIntegralJet A (linSubst g f) ↔ IsIntegralJet A f)

def IntMul : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (f f' : MvPolynomial σ R),
    IsIntegralJet A f → IsIntegralJet A f' → IsIntegralJet A (f * f')

def DerivCoeff : Prop :=
  ∀ (σ : Type u) (R : Type v) [DecidableEq σ] [CommRing R] (l : List σ) (f : MvPolynomial σ R),
    constantCoeff (l.foldr (fun i g => pderiv i g) f) =
      (mfac (Multiset.toFinsupp (l : Multiset σ)) : R) * coeff (Multiset.toFinsupp (l : Multiset σ)) f

def EvMonomial : Prop :=
  ∀ (σ : Type u) (R : Type v) [DecidableEq σ] [CommRing R] (l : List σ) (F : MvPolynomial σ R),
    evOp (monomial (Multiset.toFinsupp (l : Multiset σ)) 1) F =
      constantCoeff (l.foldr (fun i g => pderiv i g) F)

def EvIntegral : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P F : MvPolynomial σ R),
    IsIntegralJet A P → IsIntegralJet A F → evOp P F ∈ A

def EvSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (P F : MvPolynomial σ R),
    evOp P (linSubst g F) = evOp (linSubst g.transpose P) F

def EvFock : Prop :=
  ∀ (σ : Type u) (P F : MvPolynomial σ ℂ),
    evOp P F = Formalism.REAL.fockF F (map (starRingEnd ℂ) P)

def HcMatApply : Prop :=
  ∀ (R : Type v) [CommRing R] (p q : ℕ) (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R) (z : Matrix (Fin p) (Fin q) R) (a : Fin p) (b : Fin q),
    (hcMat A D).mulVec (fun x => z x.1 x.2) (a, b) = (A * z * D) a b

def HcMatMul : Prop :=
  ∀ (R : Type v) [CommRing R] (p q : ℕ) (A A' : Matrix (Fin p) (Fin p) R)
    (D D' : Matrix (Fin q) (Fin q) R),
    hcMat (A * A') (D' * D) = hcMat A D * hcMat A' D'

def HcMatInt : Prop :=
  ∀ (R : Type v) [CommRing R] (A0 : Subring R) (p q : ℕ) (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R),
    IsIntegralMat A0 A → IsIntegralMat A0 D → IsIntegralMat A0 (hcMat A D)

def ActKMul : Prop :=
  ∀ (R : Type v) [CommRing R] (p q r : ℕ) (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k k' : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    actK ρ (k * k') F = actK ρ k (actK ρ k' F)

def ActKOne : Prop :=
  ∀ (R : Type v) [CommRing R] (p q r : ℕ) (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    actK ρ 1 F = F

def ActKInt : Prop :=
  ∀ (R : Type v) [CommRing R] (A0 : Subring R) (p q r : ℕ)
    (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    IsIntegralMat A0 ((ρ k : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) →
    IsIntegralMat A0 ((k.1⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) →
    IsIntegralMat A0 ((k.2 : GL (Fin q) R) : Matrix (Fin q) (Fin q) R) →
    (∀ j, IsIntegralJet A0 (F j)) → ∀ i, IsIntegralJet A0 (actK ρ k F i)

def HomogRank : Prop :=
  ∀ (σ : Type u) (K : Type v) [Fintype σ] [Field K] (n : ℕ),
    Module.finrank K (homogeneousSubmodule σ K n) = Nat.choose (n + Fintype.card σ - 1) n

def JetRank : Prop :=
  ∀ (σ : Type u) (K : Type v) [Fintype σ] [Field K] (N : ℕ),
    Module.finrank K (restrictTotalDegree σ K N) = Nat.choose (N + Fintype.card σ) N

def JetInjective : Prop :=
  ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F) (U : Set E) (x : E),
    IsOpen U → IsPreconnected U → x ∈ U → AnalyticOnNhd ℂ f U →
    (∀ n, iteratedFDeriv ℂ n f x = 0) → Set.EqOn f 0 U

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

universe u v

def EvDualJet : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, IsIntegralJet A P → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α F ∈ A

def EvDualOp : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P : MvPolynomial σ R),
    (∀ F : MvPolynomial σ R, IsIntegralJet A F → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α P ∈ A

def EvKernel : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, evOp P F = 0) ↔ ∀ α, (mfac α : R) * coeff α F = 0

def EvSymm : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R), evOp P F = evOp F P

def EvLinear : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (c : R) (P F G : MvPolynomial σ R),
    evOp P (c • F + G) = c * evOp P F + evOp P G

def EvDegree : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R) (m n : ℕ),
    P.IsHomogeneous m → F.IsHomogeneous n → m ≠ n → evOp P F = 0

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

def partialD {n : ℕ} (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t => f (Function.update z i t)) (z i)

def partialPow {n : ℕ} (α : Fin n →₀ ℕ) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun i g => (partialD i)^[α i] g) f

def ajetCoeff {n : ℕ} (f : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ) : ℂ :=
  partialPow α f 0 / (mfac α : ℂ)

def aevOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℂ) : ℂ :=
  ∑ α ∈ P.support, coeff α P * partialPow α f 0

def AJetPoly : Prop :=
  ∀ (n : ℕ) (F : MvPolynomial (Fin n) ℂ) (α : Fin n →₀ ℕ),
    ajetCoeff (fun z => eval z F) α = coeff α F

def AEvPoly : Prop :=
  ∀ (n : ℕ) (P F : MvPolynomial (Fin n) ℂ),
    aevOp P (fun z => eval z F) = evOp P F

def AEvSubst : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
      aevOp P (fun z => f (g.mulVec z)) = aevOp (linSubst g.transpose P) f

def AJetMul : Prop :=
  ∀ (n : ℕ) (f h : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetCoeff (fun z => f z * h z) α =
        ∑ βγ ∈ Finset.HasAntidiagonal.antidiagonal α, ajetCoeff f βγ.1 * ajetCoeff h βγ.2

def AJetInjective : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
    IsOpen U → IsPreconnected U → (0 : Fin n → ℂ) ∈ U → AnalyticOnNhd ℂ f U →
      (∀ α : Fin n →₀ ℕ, partialPow α f 0 = 0) → Set.EqOn f 0 U

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open MvPolynomial

def partialDv {σ : Type} [DecidableEq σ] (i : σ) (f : (σ → ℂ) → ℂ) : (σ → ℂ) → ℂ :=
  fun z => deriv (fun t => f (Function.update z i t)) (z i)

def partialPowV {σ : Type} [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (f : (σ → ℂ) → ℂ) :
    (σ → ℂ) → ℂ :=
  (Finset.univ : Finset σ).toList.foldr (fun i g => (partialDv i)^[α i] g) f

def degLe (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.range (N + 1)).biUnion fun d => (Finset.univ : Finset σ).finsuppAntidiag d

def ajetPoly {σ : Type} [Fintype σ] [DecidableEq σ] (N : ℕ) (f : (σ → ℂ) → ℂ) :
    MvPolynomial σ ℂ :=
  ∑ α ∈ degLe σ N, monomial α (partialPowV α f 0 / (mfac α : ℂ))

def vjet {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (N : ℕ) (F : (σ → ℂ) → (Fin r → ℂ)) :
    Fin r → MvPolynomial σ ℂ :=
  fun i => ajetPoly N (fun z => F z i)

def actF {p q r : ℕ} (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)) :
    (Fin p × Fin q → ℂ) → (Fin r → ℂ) :=
  fun z => ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
    (F ((hcMat ((k.1⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ)
      ((k.2 : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec z))

def AJetPolyV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (F : MvPolynomial σ ℂ),
    ajetPoly N (fun z => eval z F) = jetTrunc N F

def AJetPolyCoeff : Prop :=
  ∀ (n N : ℕ) (f : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ), AnalyticAt ℂ f 0 →
    coeff α (ajetPoly N f) = if α.degree ≤ N then ajetCoeff f α else 0

def AJetSubstV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (g : Matrix σ σ ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ajetPoly N (fun z => f (g.mulVec z)) = linSubst g (ajetPoly N f)

def AJetMulV : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (f h : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetPoly N (fun z => f z * h z) = jetTrunc N (ajetPoly N f * ajetPoly N h)

def AJetLinear : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ) (c : ℂ) (f h : (σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetPoly N (fun z => c * f z + h z) = c • ajetPoly N f + ajetPoly N h

def ActFMul : Prop :=
  ∀ (p q r : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k k' : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)),
    actF ρ (k * k') F = actF ρ k (actF ρ k' F)

def VJetEquiv : Prop :=
  ∀ (p q r N : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ)),
    (∀ i, AnalyticAt ℂ (fun z => F z i) 0) →
      vjet N (actF ρ k F) = actK ρ k (vjet N F)

def VJetInjective : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (F : (σ → ℂ) → (Fin r → ℂ))
    (U : Set (σ → ℂ)),
    IsOpen U → IsPreconnected U → (0 : σ → ℂ) ∈ U → (∀ i, AnalyticOnNhd ℂ (fun z => F z i) U) →
      (∀ N, vjet N F = 0) → Set.EqOn F 0 U

end Formalism.MJ
end
end

section
noncomputable section

namespace Formalism.MJ

open Matrix
open scoped ComplexOrder

def blk {p q : ℕ} (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) : GL (Fin p ⊕ Fin q) ℂ where
  val := fromBlocks (A : Matrix (Fin p) (Fin p) ℂ) 0 0 (D : Matrix (Fin q) (Fin q) ℂ)
  inv := fromBlocks ((A⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0
    ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

def moeb {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * z + g.toBlocks₁₂) * (g.toBlocks₂₁ * z + g.toBlocks₂₂)⁻¹

def hcDom (p q : ℕ) : Set (Matrix (Fin p) (Fin q) ℂ) :=
  {z | (1 - zᴴ * z).PosDef}

def vecOf {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : Fin p × Fin q → ℂ := fun x => z x.1 x.2

def moebiusJetDuality : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
      (A : Matrix (Fin p) (Fin p) ℂ) * z * ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)

def moebiusJetDualityReformulated : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ),
    blk A D ∈ Formalism.UG.Upq p q ↔
      ((A : Matrix (Fin p) (Fin p) ℂ)ᴴ * (A : Matrix (Fin p) (Fin p) ℂ) = 1 ∧
        (D : Matrix (Fin q) (Fin q) ℂ)ᴴ * (D : Matrix (Fin q) (Fin q) ℂ) = 1)

def StabZero : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ), g ∈ Formalism.UG.Upq p q →
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = 0 → g ∈ Formalism.UG.blockDiag p q

def MoebTangent : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    vecOf (moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) =
      (hcMat (A : Matrix (Fin p) (Fin p) ℂ) ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec
        (vecOf z)

def ActFMoeb : Prop :=
  ∀ (p q r : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ))
    (z : Matrix (Fin p) (Fin q) ℂ),
    actF ρ k F (vecOf z) = ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
      (F (vecOf (moeb (((blk k.1 k.2)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)))

def MoebDom : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      IsUnit ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂).det ∧
      moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q

def MoebMul : Prop :=
  ∀ (p q : ℕ) (g h : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → h ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      moeb ((g * h : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
        moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
          (moeb (h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)

def ZeroMemDom : Prop := ∀ p q : ℕ, (0 : Matrix (Fin p) (Fin q) ℂ) ∈ hcDom p q

end Formalism.MJ
end
end

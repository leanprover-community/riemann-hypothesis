import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)

def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)

def CondC {r K : ℕ} (isVec : ℕ → Bool) (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ) (i : ℕ) : Prop :=
  ∀ (a : Fin r) (b : Fin K), a.val + 1 = r → b.val = 0 →
    if isVec i then κ (i + 1) b ≤ ν i a else κ i b ≤ ν (i + 1) a

def StripPathSplitting : Prop :=
  ∀ (r K N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), 1 ≤ r → 1 ≤ K →
    (∀ μ : ℕ → Fin (r + K) → ℤ,
      IsPath (r + K) isVec B μ N ↔
        ∃ b' b'' : ℕ → ℕ, (∀ i < N, b' i + b'' i = B i) ∧
          IsPath r isVec b' (fun i a => μ i (Fin.castAdd K a)) N ∧
          IsPath K isVec b'' (fun i b => μ i (Fin.natAdd r b)) N ∧
          ∀ i < N, CondC isVec (fun i a => μ i (Fin.castAdd K a)) (fun i b => μ i (Fin.natAdd r b)) i) ∧
    (∀ (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ),
      (fun i a => (Fin.append (ν i) (κ i)) (Fin.castAdd K a)) = ν ∧
      (fun i b => (Fin.append (ν i) (κ i)) (Fin.natAdd r b)) = κ)

def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card

def PathColumns : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ), IsPath n isVec B μ N →
    (∀ i ≤ N, ∀ c (m : Fin n), c ≤ μ i m ↔ m.val < colHeight (μ i) c) ∧
    (∀ c : ℤ, colHeight (μ 0) c = if 1 ≤ c then 0 else n) ∧
    (∀ i < N, ∀ c : ℤ,
      if isVec i then
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
      else
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c) ∧
    (∀ i < N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.ncard = B i)

variable {ι : Type*}

def ordW (r K : ℕ) (isVec : ι → Bool) (om : ι → ℝ) : ι × Fin (r + K) → ℝ :=
  fun x => if (isVec x.1 = true ↔ r ≤ x.2.val) then om x.1 else 0

def OrdGe {σ R : Type*} [CommRing R] (w : σ → ℝ) (f : MvPolynomial σ R) (o : ℝ) : Prop :=
  ∀ e ∈ f.support, o ≤ Finsupp.weight w e

def colOrd (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (om : ι → ℝ) (l : ℕ) : ℝ :=
  ∑ m ∈ (range l).filter (fun m => colCostly r primal isVec lt m), om (lt m)

def rowX (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin (r + K) → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, a)

def rowPl (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin r → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, Fin.castAdd K a)

def rowNm (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin K → MvPolynomial (ι × Fin (r + K)) R :=
  fun b => X (i, Fin.natAdd r b)

def LowestPart (R : Type*) [CommRing R] (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ) : Prop :=
  ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
    OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) l I) (colOrd r primal isVec lt om l) ∧
    weightedHomogeneousComponent (ordW r K isVec om) (colOrd r primal isVec lt om l)
        (colWord primal isVec lt (rowX R r K) l I) =
      joinF (colPl primal isVec lt (rowPl R r K) l) (colTan r primal isVec lt (rowNm R r K) l) I

def LowestComponent : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L

def LemmaB2plus : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    ∀ l < L, ∀ I : Finset (Fin (r + K)),
      (if primal then ((planePart I).card : ℤ) < min (colDeg primal isVec lt (l + 1)) (r : ℤ)
        else (planePart I).Nonempty) →
      OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) (l + 1) I)
        (colOrd r primal isVec lt om (l + 1) + om (lt l))

def LemmaB2tie : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) ≤ om (lt l)) →
    (∀ l, l + 1 < L → colCostly r primal isVec lt (l + 1) → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L

def LemmaB2necessity : Prop :=
  ¬ LowestPart ℤ 1 1 true (fun i : Fin 2 => decide (i = 0)) (fun l => if l = 0 then 0 else 1)
      (fun _ => 1) 2

def FirstStepFree : Prop :=
  ∀ (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ L →
    ColValid r K primal isVec lt L → ¬ colCostly r primal isVec lt 0

def SymbolWordSupport : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L → Set.InjOn lt (Set.Iio L) →
    ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
      (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I ≠ 0 →
        Nominal primal I ∧ (I.card : ℤ) = colDeg primal isVec lt l) ∧
      ∀ i : ι, IsWeightedHomogeneous (fun x : ι × Fin (r + K) => if x.1 = i then 1 else 0)
        (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I)
        (if ∃ m < l, lt m = i then 1 else 0)

def SymbolWordJoin : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (pl : ι → Fin r → R) (nm : ι → Fin K → R) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    ∀ l ≤ L, symWord primal isVec lt pl nm l =
      joinF (colPl primal isVec lt pl l) (colTan r primal isVec lt nm l)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def nthElt {n : ℕ} (J : Finset (Fin n)) (a : ℕ) : ℕ := ((J.sort (· ≤ ·)).map Fin.val).getD a n

def SemiStd {n C : ℕ} (T : Fin C → Finset (Fin n)) : Prop :=
  ∀ c c' : Fin C, c.val + 1 = c'.val → ∀ a < (T c').card, nthElt (T c) a ≤ nthElt (T c') a

def initSeg (n h : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < h

def genX (k : Type*) [CommRing k] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b => X (a, b)

def tabMinors (k : Type*) [CommRing k] {n C : ℕ} (T : Fin C → Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) k :=
  ∏ c, minorF (genX k n) (initSeg n (T c).card) (T c)

def tabDiag {n C : ℕ} (T : Fin C → Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ c, ∑ b ∈ T c, ∑ a : Fin n,
    if a.val = ((T c).filter (· < b)).card then Finsupp.single (a, b) 1 else 0

def LeadingMinors : Prop :=
  ∀ (k : Type) [CommRing k] (n C : ℕ) (T : Fin C → Finset (Fin n)),
    coeff (tabDiag T) (tabMinors k T) = 1 ∧
    (∀ e ∈ (tabMinors k T).support, e ≠ tabDiag T →
      ∃ x : Fin n × Fin n, e x < tabDiag T x ∧
        ∀ y : Fin n × Fin n, (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2)) → e y = tabDiag T y) ∧
    (∀ T' : Fin C → Finset (Fin n), SemiStd T → SemiStd T' → tabDiag T = tabDiag T' → T = T')

def LemmaA : Prop :=
  ∀ (k : Type) [Field k] (n C : ℕ),
    LinearIndependent k (fun T : {T : Fin C → Finset (Fin n) // SemiStd T} => tabMinors k T.1)

def pathWord {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | i + 1 =>
    if colHeight (μ (i + 1)) c = colHeight (μ i) c then pathWord isVec μ c Xr i
    else stepF (isVec i == decide (1 ≤ c)) (pathWord isVec μ c Xr i) (Xr i)

def canIdx {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) : Finset (Fin n) :=
  if 1 ≤ c then univ.filter fun m => m.val < colHeight μN c
  else univ.filter fun m => colHeight μN c ≤ m.val

def psiPath (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ᶠ c : ℤ, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)

def IsIndex {n : ℕ} (μN : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  ∀ c : ℤ, (I c).card = if 1 ≤ c then colHeight μN c else n - colHeight μN c

def PathWordIsColWord : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (c : ℤ), IsPath n isVec B μ N →
    ∃ (L : ℕ) (lt : ℕ → ℕ), StrictMono lt ∧ (∀ l < L, lt l < N) ∧
      (∀ i < N, colHeight (μ (i + 1)) c ≠ colHeight (μ i) c ↔ ∃ l < L, lt l = i) ∧
      (∀ l ≤ L, 0 ≤ colDeg (decide (1 ≤ c)) isVec lt l ∧ colDeg (decide (1 ≤ c)) isVec lt l ≤ (n : ℤ)) ∧
      (∀ l < L, colDeg (decide (1 ≤ c)) isVec lt l =
        if 1 ≤ c then (colHeight (μ (lt l)) c : ℤ) else (n : ℤ) - colHeight (μ (lt l)) c) ∧
      (colDeg (decide (1 ≤ c)) isVec lt L =
        if 1 ≤ c then (colHeight (μ N) c : ℤ) else (n : ℤ) - colHeight (μ N) c) ∧
      ∀ (R : Type) [CommRing R] (Xr : ℕ → Fin n → R),
        pathWord isVec μ c Xr N = colWord (decide (1 ≤ c)) isVec lt Xr L

def PsiDegrees : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)).Finite ∧
    ∀ i : ℕ, IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (psiPath R isVec μ N I) (if i < N then B i else 0)

def expE (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (a b : Fin n) :
    MvPolynomial (ℕ × Fin n) R →ₐ[R] Polynomial (MvPolynomial (ℕ × Fin n) R) :=
  aeval fun x =>
    if isVec x.1 then
      (if x.2 = b then Polynomial.C (X x) + Polynomial.X * Polynomial.C (X (x.1, a)) else Polynomial.C (X x))
    else
      (if x.2 = a then Polynomial.C (X x) - Polynomial.X * Polynomial.C (X (x.1, b)) else Polynomial.C (X x))

def LemmaA1hw : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ N →
    (∀ m : Fin n, IsWeightedHomogeneous
      (fun x : ℕ × Fin n => if x.2 = m then (if isVec x.1 then (1 : ℤ) else -1) else 0)
      (psiPath R isVec μ N (canIdx (μ N))) (μ N m)) ∧
    ∀ a b : Fin n, a < b →
      expE R isVec a b (psiPath R isVec μ N (canIdx (μ N))) =
        Polynomial.C (psiPath R isVec μ N (canIdx (μ N)))

def PathProductLinearIndependent : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (ν : Fin n → ℤ),
    LinearIndependent k
      (fun P : {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0} =>
        psiPath k isVec P.1 N (canIdx ν))

def LemmaA1lead : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ (N + 1) →
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ e : ℕ × Fin n →₀ ℕ, (∀ x ∈ e.support, x.1 < N) →
        coeff (e + ∑ m : Fin n, Finsupp.single (N, m) (|μ (N + 1) m - μ N m|).toNat)
            (psiPath R isVec μ (N + 1) (canIdx (μ (N + 1)))) =
          (ε : R) * coeff e (psiPath R isVec μ N (canIdx (μ N)))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

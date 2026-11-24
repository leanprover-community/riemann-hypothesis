module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def Cell (K : Type*) [Fintype K] (ι : K → Type*) (n : ℕ) : Type _ :=
  {I : ∀ k, Finset (ι k) // (∀ k, (I k).Nonempty) ∧ ∑ k, ((I k).card - 1) = n}

def cellMon (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} (I : ∀ k, Finset (ι k)) :
    Submonoid (MRingOver S ι) :=
  Submonoid.closure {f | ∃ k, ∃ i ∈ I k, f = X ⟨k, i⟩}

abbrev CechC (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) (M : Type*)
    [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) : Type _ :=
  ∀ I : Cell K ι n, LocalizedModule (cellMon S I.1) M


open Classical in
def cellRes (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} (M : Type*) [AddCommGroup M]
    [Module (MRingOver S ι) M] (J I : ∀ k, Finset (ι k)) :
    LocalizedModule (cellMon S J) M →ₗ[MRingOver S ι] LocalizedModule (cellMon S I) M := by
  classical
  exact if h : cellMon S J ≤ cellMon S I then LocalizedModule.liftOfLE _ _ h else 0

def faceSign {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*} [∀ k, LinearOrder (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) : ℤ :=
  (-1) ^ (((I k).filter (· < i)).card + ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1))


def cechD (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, LinearOrder (ι k)] (M : Type*) [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) :
    CechC S ι M n →ₗ[MRingOver S ι] CechC S ι M (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • (cellRes S M _ I.1).comp
        (LinearMap.proj (R := MRingOver S ι) (φ := fun J : Cell K ι n => LocalizedModule (cellMon S J.1) M)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
    else 0

def IsMGraded (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) : Prop :=
  DirectSum.IsInternal 𝓜 ∧
    ∀ (a : K → ℕ) (c : K → ℤ) (p : MRingOver S ι) (m : M), IsMultiHomog p a → m ∈ 𝓜 c →
      p • m ∈ 𝓜 (c + fun k => (a k : ℤ))

def locPart {S : Type*} [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι))
    (c : K → ℤ) : Submodule S (LocalizedModule T M) :=
  Submodule.span S {x | ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
    m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t}

def cechCc {S : Type*} [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Submodule S (CechC S ι M n) :=
  Submodule.pi Set.univ fun I => locPart ι 𝓜 (cellMon S I.1) c

def cechZc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Submodule S (CechC S ι M n) :=
  cechCc ι 𝓜 c n ⊓ (LinearMap.ker (cechD S ι M n)).restrictScalars S

def cechBc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) :
    (n : ℕ) → Submodule S (CechC S ι M n)
  | 0 => ⊥
  | n + 1 => (cechCc ι 𝓜 c n).map ((cechD S ι M n).restrictScalars S)

abbrev cechHc {S : Type*} [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) : Type _ :=
  ↥(cechZc ι 𝓜 c n) ⧸ (cechBc ι 𝓜 c n).comap (cechZc ι 𝓜 c n).subtype

def cechMap (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) {M N : Type*}
    [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N]
    (g : M →ₗ[MRingOver S ι] N) (n : ℕ) : CechC S ι M n →ₗ[MRingOver S ι] CechC S ι N n :=
  LinearMap.pi fun I => (IsLocalizedModule.map (cellMon S I.1) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) g).comp
      (LinearMap.proj (R := MRingOver S ι) (φ := fun J : Cell K ι n => LocalizedModule (cellMon S J.1) M) I)

def IsMGradedMap (S : Type*) [CommRing S] {K : Type*} (ι : K → Type*) {M N : Type*}
    [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [AddCommGroup N] [Module (MRingOver S ι) N]
    [Module S N] (𝓜 : (K → ℤ) → Submodule S M) (𝓝 : (K → ℤ) → Submodule S N)
    (g : M →ₗ[MRingOver S ι] N) : Prop :=
  ∀ c, ∀ m ∈ 𝓜 c, g m ∈ 𝓝 c

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

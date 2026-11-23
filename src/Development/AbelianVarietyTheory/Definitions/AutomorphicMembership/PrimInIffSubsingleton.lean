module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst
public import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩


variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

end Lattice

end GlobalTheory.IntTerm

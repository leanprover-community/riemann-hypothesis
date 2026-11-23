module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)

def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)

def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin

def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin

def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)

def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2

def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl


omit [NumberField E] in
theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl




omit [NumberField E] in
theorem mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := Iff.rfl









end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]


theorem latMap_one (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]

theorem latMap_mul (γ δ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (γ * δ) Λ = latMap γ (latMap δ Λ) := by
  rw [latMap, latMap, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
  rfl

end Iso

section Unip

variable {n r : ℕ}

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Examples

end GlobalTheory.SgGlob

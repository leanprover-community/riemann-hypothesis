module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

def GenIx {S : Type} (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

abbrev GenField (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : Type :=
  FractionRing (MvPolynomial (GenIx r) Ω)

def genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) :
    Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun l k =>
  if h : k < l then algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩)
  else if l = k then 1 else 0

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

def genB (c : ∀ s, Fin (r s) → E) (s : S) (k : Fin (r s)) : TensorProduct Ω (GenField Ω r) E :=
  ∑ l, genU Ω r s l k • TensorProduct.mk Ω (GenField Ω r) E 1 (c s l)

def flagMat {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) * genU Ω r s

def FlagIx (κ : Type) {S : Type} (n : S → ℕ) (r : S → ℕ) : Type :=
  κ × ((q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))

def flagCoord [Fintype S] (κ : Type) (x : κ → Ω) {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) : FlagIx κ n r → GenField Ω r := fun cJ =>
  algebraMap Ω (GenField Ω r) (x cJ.1) *
    ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (cJ.2 q) (Fin.castLE q.2.2)).det

def IsTwistGen {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (L : Lat ξ E) (m : ℕ)
    {n : ℕ} (φ : Fin n → Module.Dual Ω E) : Prop :=
  (∀ j (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ j e / x c ^ m ∈ regAt ξ p) ∧
  ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ j, g j * (φ j e / x c ^ m)

theorem coordTie_comp_equiv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by
  have hch : ∀ c p, InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
    intro c p
    simp only [InChart, Function.comp]
    exact and_congr Iff.rfl ⟨fun h c' => by simpa using h (e.symm c'), fun h c' => h (e c')⟩
  have hr : ∀ c, Set.range (fun j => (x ∘ e) j / (x ∘ e) c) = Set.range (fun j => x j / x (e c)) := by
    intro c
    ext a
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hch _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => by rw [hq q]; exact exists_congr fun h' => (hch c _).symm⟩
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hch c p).symm Iff.rfl
end GlobalTheory.CompanionTheory.Ar.FlagBun

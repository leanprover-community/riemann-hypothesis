module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

def FinAlg (T : Set ℂ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧ T ⊆ (Subfield.closure (Z : Set ℂ) : Set ℂ)

theorem FinAlg.mono {T T' : Set ℂ} (h : FinAlg T') (hT : T ⊆ T') : FinAlg T := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, hT.trans hsub⟩

theorem finAlg_of_finite {T : Set ℂ} (h : T.Finite) (ha : ∀ z ∈ T, IsAlgebraic ℚ z) : FinAlg T := by
  refine ⟨h.toFinset, fun z hz => ha z (h.mem_toFinset.mp hz), ?_⟩
  rw [h.coe_toFinset]
  exact Subfield.subset_closure

theorem finAlg_biUnion {κ : Type} {s : Set κ} (hs : s.Finite) {T : κ → Set ℂ} (h : ∀ k ∈ s, FinAlg (T k)) :
    FinAlg (⋃ k ∈ s, T k) := by
  classical
  choose! Z hZ hsub using h
  refine ⟨hs.toFinset.biUnion Z, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact hZ k (hs.mem_toFinset.mp hk) z hzk
  · refine Set.iUnion₂_subset fun k hk => (hsub k hk).trans (Subfield.closure_mono ?_)
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨k, hs.mem_toFinset.mpr hk, hz⟩

theorem FinAlg.union {T T' : Set ℂ} (h : FinAlg T) (h' : FinAlg T') : FinAlg (T ∪ T') := by
  classical
  obtain ⟨Z, hZ, hsub⟩ := h
  obtain ⟨Z', hZ', hsub'⟩ := h'
  refine ⟨Z ∪ Z', fun z hz => ?_, Set.union_subset ?_ ?_⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact hZ z hz
    · exact hZ' z hz
  · exact hsub.trans (Subfield.closure_mono (by simp))
  · exact hsub'.trans (Subfield.closure_mono (by simp))

theorem FinAlg.closure {T : Set ℂ} (h : FinAlg T) : FinAlg (Subfield.closure T : Set ℂ) := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr hsub)⟩

variable {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ)

def jetSet (n : ℕ) : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b)
    (e : DVar X.Tau a b →₀ ℕ), InRange S M c N N' x ∧ e.degree = n ∧
      z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) e}

def JetAlg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange S M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      IsAlgebraic ℚ ((A.chiF a b N N')⁻¹ * derivAt0 (A.thInd S N N' c x) e)

def VacEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

end GlobalTheory.Mem.Col2.JetEx

end

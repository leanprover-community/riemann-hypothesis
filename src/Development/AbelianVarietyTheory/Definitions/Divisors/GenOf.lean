module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW

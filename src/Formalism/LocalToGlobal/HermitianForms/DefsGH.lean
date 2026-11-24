module

public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

structure GLevH (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
    (lam : ∀ a v h, H a v h →* ℂˣ) where

  fr : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletion F)
  fr_lat : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) (x : Fin n → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ b, G.phi a v h (y b) = x b) ↔
      ∀ b, (((fr a v h)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  mem : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb,
    x ∈ S.Uloc v ↔ ∃ M ∈ H a v h, (M : Matrix (Fin n) (Fin n) (kv F v)) = redM F v (G.mat a v h (fr a v h) x)

  red : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), S.U → H a v h
  red_eq : ∀ a v h (x : S.U), (((red a v h x : H a v h) : GL (Fin n) (kv F v)) : Matrix (Fin n) (Fin n) (kv F v)) =
    redM F v (G.mat a v h (fr a v h) (bc (prV (E := E) v) x.1))

  chi_eq : ∀ x : S.U, (S.chi x : ℂ) = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal),
    (((lam a v h (red a v h x) : ℂˣ) : ℂ))⁻¹

  chi_unit : ∀ x : S.U, ‖(S.chi x : ℂ)‖ = 1


end Formalism.L2.Forms

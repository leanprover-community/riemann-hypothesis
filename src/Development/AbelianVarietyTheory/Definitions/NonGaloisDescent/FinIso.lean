module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.FormDict

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinIso where
  κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L
  left : ∀ x : L, κ (x ⊗ₜ 1) = algebraMap L _ x
  right : ∀ (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))), NG.OverPl w v →
    ∃ i : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L, Continuous i ∧
      ∀ a : FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L), κ (1 ⊗ₜ a) w = i (a v)
  j : GAf L n →* UA L n
  fin : ∀ x, j x ∈ finU (E := L) (n := n)
  loc : ∀ (x : GAf L n) (w : HeightOneSpectrum (𝓞 L)) (s t : Fin n),
    (cLoc w (j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) w
  onto : ∀ y ∈ finU (E := L) (n := n), ∃ x, j x = y

variable {L n}

def Dict (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)) : Prop :=
  IsAutRepU U ∧ U.map (LinearMap.funLeft ℂ ℂ F.j) =
    Submodule.span ℂ {φ | ∃ f ∈ π.S, ∃ lam : Module.Dual ℂ π.W, φ = fun x => lam (f x)}

end GlobalTheory.FormDict

end

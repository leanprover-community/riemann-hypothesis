module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KUTransfer

theorem ku_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  intro L _ _ _ n w σ b hb p hp x
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  have hK : ∀ g : GL (Fin n) (w.adicCompletion L), g ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      g ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := by
    intro g
    show g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L w) ↔ _
    rw [hO]; rfl
  have h1 : p x ∈ Formalism.UG.KU σ n ↔ (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [hK]
    show (p x).val ∈ Formalism.UG.intPts (Formalism.UG.intL _).subtype (Formalism.UG.GU σ n) ↔ _
    exact ⟨fun h => h.2, fun h => ⟨(p x).2, h⟩⟩
  rw [h1, hp]
  have hbi : b⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hb
  constructor
  · intro h
    have := (GlobalTheory.LFun.KGL w (n := n)).mul_mem (( GlobalTheory.LFun.KGL w (n := n)).mul_mem hb h) hbi
    simpa [mul_assoc] using this
  · intro h
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem hbi h) hb

end GlobalTheory.KUTransfer

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalf
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  first | exact @GlobalTheory.UnipModHalf.unip_mod_half | exact GlobalTheory.UnipModHalf.unip_mod_half | (intros; apply GlobalTheory.UnipModHalf.unip_mod_half <;> assumption)

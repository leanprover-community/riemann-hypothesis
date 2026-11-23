module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalFieldData
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inertPlace_localField_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * ptAt hw h z)) := by
  first | exact @GlobalTheory.InertPsi.exists_field_data | exact GlobalTheory.InertPsi.exists_field_data | (intros; apply GlobalTheory.InertPsi.exists_field_data <;> assumption)

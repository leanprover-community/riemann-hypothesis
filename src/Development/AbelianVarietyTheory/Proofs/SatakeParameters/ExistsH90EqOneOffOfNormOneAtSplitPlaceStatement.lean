module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsH90EqOneOffOfNormOneAtSplitPlace
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_normOne_oneOff_at_split_place_forall : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F), (∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x)) → ∀ (π : (AfE F E)ˣ), π ∈ U1 σ → OneOff w π → ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place | exact GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place <;> assumption)

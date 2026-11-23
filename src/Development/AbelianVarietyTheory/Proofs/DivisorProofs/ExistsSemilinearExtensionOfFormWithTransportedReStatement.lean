module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearExtensionOfFormWithTransportedRe
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

theorem _root_.GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep : ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  first | exact @GlobalTheory.SemilinearReading.exists_semilinear_extension_rep | exact GlobalTheory.SemilinearReading.exists_semilinear_extension_rep | (intros; apply GlobalTheory.SemilinearReading.exists_semilinear_extension_rep <;> assumption)

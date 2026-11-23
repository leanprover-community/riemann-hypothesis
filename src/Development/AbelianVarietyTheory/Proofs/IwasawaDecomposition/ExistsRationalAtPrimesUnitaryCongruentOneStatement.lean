module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalAtPrimesUnitaryCongruentOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev


theorem _root_.GlobalTheory.T.exists_rationalAtPrimes_unitary_congruentOne : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 E))}, (∀ P ∈ Q, conjPrime₂ P ∉ Q) →
    ∀ (m : ℕ), 0 < m → (∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) → ∀ (z : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    z ∈ St (1 : GL (Fin n) (AfE F E)) →
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  first | exact @GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne | exact GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne | (intros; apply GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne <;> assumption)

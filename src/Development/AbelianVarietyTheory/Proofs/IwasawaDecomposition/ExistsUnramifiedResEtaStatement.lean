module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_unramified_resEta_alt : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) * ∏ w : InfinitePlace F, etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  first | exact @GlobalTheory.Mem.EtaExt.exists_unramified_resEta | exact GlobalTheory.Mem.EtaExt.exists_unramified_resEta | (intros; apply GlobalTheory.Mem.EtaExt.exists_unramified_resEta <;> assumption)

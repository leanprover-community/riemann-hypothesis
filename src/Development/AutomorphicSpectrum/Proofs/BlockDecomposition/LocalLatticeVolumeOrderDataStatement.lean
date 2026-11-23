module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeVolumeOrderData
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_lattice_volume_order_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M j : ℕ), IsCompact (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∧ IsOpen (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | exact GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | (intros; apply GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen <;> assumption)

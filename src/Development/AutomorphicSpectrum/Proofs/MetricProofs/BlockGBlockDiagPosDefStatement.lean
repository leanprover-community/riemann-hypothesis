module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
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

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.blockG_blockDiag_posDef : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef <;> assumption)

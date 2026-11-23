module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.commonStabilizerFromCoordinates_product_law : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  first | exact @GlobalTheory.DegVol.RefCovMul.crd_mul | exact GlobalTheory.DegVol.RefCovMul.crd_mul | (intros; apply GlobalTheory.DegVol.RefCovMul.crd_mul <;> assumption)

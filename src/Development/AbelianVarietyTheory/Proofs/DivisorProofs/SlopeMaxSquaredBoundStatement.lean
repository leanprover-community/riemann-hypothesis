module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_max_squared_bound : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A => slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  first | exact @GlobalTheory.CovTop.LamCore.lamCore | exact GlobalTheory.CovTop.LamCore.lamCore | (intros; apply GlobalTheory.CovTop.LamCore.lamCore <;> assumption)

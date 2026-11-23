module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiBigTheorem.HSChain
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiSymmetry.EqMapSymm
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
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

@[expose] public section

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

theorem moriwakiBig_outright : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  moriwakiBig_of_classicalTheorems PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

theorem hsUse_outright : HSUse :=
  hsUse_of_hypotheses PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

end PositivityTheory.Pf1.HilbertSamuelMoriwaki

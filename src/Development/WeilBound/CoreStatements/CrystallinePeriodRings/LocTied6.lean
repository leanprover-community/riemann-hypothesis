module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open Loc
open scoped Formalism.Per6

structure LocTied6 (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) where

  eB : P.R.B ≃+* Per6.Bcris l

  eD : P.R.BdR ≃+* Per6.BdR l

  zB : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] P.R.B (z : ℚ_[l])) = Per6.zB l z

  zD : ∀ z : ℤ_[l], eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) = Per6.zD l z

  om : ∀ x : Om l, ∃ y : Per6.BdRp l, eD (algebraMap (Om l) P.R.BdR x) = algebraMap (Per6.BdRp l) (Per6.BdR l) y ∧
    Per6.θD l y = ((x : Om l) : ℂ_[l])

  actB : ∀ (g : GQ l) (b : P.R.B), eB (P.actQ g b) = Per6.σB g (eB b)

  actD : ∀ (g : GQ l) (b : P.R.BdR), eD (P.actQdR g b) = Per6.σD g (eD b)

  frob : ∀ b : P.R.B, eB (P.φB b) = Per6.φB l (eB b)

  incl : Per6.IsCrisDR l ((eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp eB.symm.toRingHom)

  fil : ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔ eD x ∈ Per6.FilD l a

  t : ∃ y : Per6.BdRp l, Per6.IsLog l AI.ε y ∧ eD (P.ιB P.tB) = algebraMap (Per6.BdRp l) (Per6.BdR l) y

  ιA : ∀ a : Ainf l, eB (AI.ιA a) = Per6.aB l a

end Formalism.BasicNotions

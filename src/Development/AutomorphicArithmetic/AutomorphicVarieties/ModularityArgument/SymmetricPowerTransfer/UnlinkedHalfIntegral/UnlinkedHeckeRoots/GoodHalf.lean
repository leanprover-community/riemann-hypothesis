module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConjEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PrimCj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SelfAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SqrtFlip
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

theorem goodHalf : GoodHalf := by
  intro k N _ hk χ hχ g hg p hp hpN α β hs hm
  obtain ⟨σ, hσ⟩ := sqrtFlip p hp
  obtain ⟨g', hg'⟩ := conjEig k N χ g hg σ
  have hu : IsUnit ((p : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  have h1 : ‖χ (p : ZMod N)‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    simpa using this
  have e : cj σ χ (p : ZMod N) = σ (χ (p : ZMod N)) := rfl
  have h2 : ‖σ (χ (p : ZMod N))‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one (cj σ χ) hu.unit
    rw [IsUnit.unit_spec, e] at this
    exact this
  have a1 := selfAdj k N hk χ hχ g p hp hpN
  have a2 := selfAdj k N hk (cj σ χ) (primCj N χ σ hχ) g' p hp hpN
  rw [hg' p hp.one_lt.le, e] at a2
  exact halfAlg p (k - 1) (g.a p) (χ (p : ZMod N)) α β σ hp.two_le h1 h2 hσ a1 a2 hs hm

end UpperTheory.V.Z.Sym.Unl

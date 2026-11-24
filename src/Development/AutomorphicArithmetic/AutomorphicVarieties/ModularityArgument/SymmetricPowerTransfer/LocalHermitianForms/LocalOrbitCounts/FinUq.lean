module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SemiSemi
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finUq : UpperTheory.V.Z.Sym.Loc.FinUq := by
  intro O K _ _ _ _ _ Δ τ L c d m h δ ι P hM
  refine ⟨orbEq O K Δ τ L c d m h δ ι P hM, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := finU O K Δ τ L c d m h δ ι P hM
    refine ⟨s, fun y hy => hs y ?_⟩
    by_contra hn
    exact hy (by simp [UpperTheory.V.Z.Sym.Glob.one, hn])
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro y
    have e : MulAction.stabilizer (U3 Δ) (QuotientGroup.mk y : U3 Δ ⧸ KU O Δ)
        = (KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom := by
      ext g
      simp [MulAction.mem_stabilizer_iff, QuotientGroup.eq, mul_assoc]
      constructor
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
    rw [e]
    exact stabU O K Δ τ L c d m h δ ι P hM y

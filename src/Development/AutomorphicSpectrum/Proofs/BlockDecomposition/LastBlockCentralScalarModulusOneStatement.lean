module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOne
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.last_block_central_scalar_modulus_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), j.val + 1 = h → leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧ modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  intro k _ _ _ _ h N d hd t j hj
  open GlobalTheory.CompanionTheory.ZjScalar in
    constructor
    · apply Units.ext
      ext p q
      obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
      obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, zj_last d t j hj a]
        by_cases hxy : x = y
        · subst hxy
          simp [Matrix.GeneralLinearGroup.scalar]
        · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
          simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
          hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
        rw [leviEmb_apply_ne k _ _ hab]
        simp [Matrix.GeneralLinearGroup.scalar, this]
    · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
      simp only [modulus, nabs_det_zj_last d t j hj]
      have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
          nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
        rw [zpow_mul, zpow_natCast]
      simp only [this]
      rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]

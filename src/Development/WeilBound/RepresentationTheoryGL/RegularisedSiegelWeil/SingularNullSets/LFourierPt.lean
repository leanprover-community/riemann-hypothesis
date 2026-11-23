module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFourierPt

variable {D : D7} {n : ℕ}

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : Matrix (Fin n) (Fin n) D.host.E)
    (x : Mx D n n) : conj (pch ψ x (rat a)) = ψ (-GlobalTheory.CompanionTheory.FourierN.pr a x) := by
  have e : pch ψ x (rat a) = ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) := by
    rw [pch, GlobalTheory.CompanionTheory.FourierN.pr]
    congr 2
    exact Matrix.trace_mul_comm _ _
  rw [e, AddChar.map_neg_eq_inv]
  have hn : ‖ψ (GlobalTheory.CompanionTheory.FourierN.pr a x)‖ = 1 := hψ.2.1 _
  have hne : ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

end PositivityTheory.Rg.Rsw.L.LFourierPt

namespace PositivityTheory.Rg.Rsw.L

open LFourierPt


theorem fourierPt : FourierPt := by
  intro D n ψ hψ lam 𝓖 hC f hf hper hco
  obtain ⟨hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) :=
    GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (hermA D n) (ratHerm D n) K hK hcov
    (GlobalTheory.CompanionTheory.FourierN.hermSub D n) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩),
      fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lam 𝓖 hlam hFD f hf hper
    (fun a => by
      have h := hco ⟨a.1, a.2⟩
      refine (integral_congr_ae (.of_forall fun x => ?_)).trans h
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1) * f x = f x * conj (pch ψ x.1 (rat a.1))
      rw [conj_pch hψ, mul_comm])

end PositivityTheory.Rg.Rsw.L

end

module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLawStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcShift




theorem zc_shift : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  intro D n ρ p hn M m ψ hψ b₀ F hF c h
  obtain ⟨hadd, hnorm, hrat, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  obtain ⟨hl, hFD, -⟩ := m.hz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := countable_of_Lindelof_of_discrete
  have hnz : ∀ z z' : hermA D ρ, M.nzx z 0 * M.nzx z' 0 = M.nzx (z + z') 0 := fun z z' => by
    have := GlobalTheory.T.unipotent_heisenberg_mul M z z' 0 0
    rwa [add_zero] at this
  have hconj : conj (chz ψ b₀ c) * chz ψ b₀ c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  set u : hermA D ρ → ℂ := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) with hu
  have hper : ∀ γ ∈ ratHerm D ρ, ∀ x, u (γ + x) = u x := by
    intro γ hγ x
    simp only [hu]
    rw [← hnz, mul_assoc, hF _ ((GlobalTheory.T.rational_points_heisenberg_group M).2.2 γ hγ), hadd, hrat γ hγ, one_mul]
  have hpt : ∀ z : hermA D ρ, F (M.nzx z 0 * (M.nzx c 0 * h)) * conj (chz ψ b₀ z) = chz ψ b₀ c * u (z + c) := by
    intro z
    simp only [hu]
    rw [← mul_assoc, hnz, hadd, map_mul]
    linear_combination (-(F (M.nzx (z + c) 0 * h) * conj (chz ψ b₀ z))) * hconj
  unfold zc
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  exact GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D ρ) m.lz hFD u hper c

end GlobalTheory.CompanionTheory.ZcShift

end
